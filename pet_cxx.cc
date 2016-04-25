/*
 * Copyright 2011      Leiden University. All rights reserved.
 * Copyright 2012-2014 Ecole Normale Superieure. All rights reserved.
 * 
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 
 *    1. Redistributions of source code must retain the above copyright
 *       notice, this list of conditions and the following disclaimer.
 * 
 *    2. Redistributions in binary form must reproduce the above
 *       copyright notice, this list of conditions and the following
 *       disclaimer in the documentation and/or other materials provided
 *       with the distribution.
 * 
 * THIS SOFTWARE IS PROVIDED BY LEIDEN UNIVERSITY ''AS IS'' AND ANY
 * EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR
 * PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL LEIDEN UNIVERSITY OR
 * CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
 * EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
 * PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA,
 * OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 * THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 * 
 * The views and conclusions contained in the software and documentation
 * are those of the authors and should not be interpreted as
 * representing official policies, either expressed or implied, of
 * Leiden University.
 */ 

#include "config.h"

#include <stdlib.h>
#include <map>
#include <vector>
#include <iostream>
#ifdef HAVE_ADT_OWNINGPTR_H
#include <llvm/ADT/OwningPtr.h>
#else
#include <memory>
#endif
#include <llvm/Support/raw_ostream.h>
#include <llvm/Support/ManagedStatic.h>
#include <llvm/Support/Host.h>
#include <clang/Basic/Version.h>
#include <clang/Basic/FileSystemOptions.h>
#include <clang/Basic/FileManager.h>
#include <clang/Basic/TargetOptions.h>
#include <clang/Basic/TargetInfo.h>
#include <clang/Driver/Compilation.h>
#include <clang/Driver/Driver.h>
#include <clang/Driver/Tool.h>
//#include <clang/Frontend/CompilerInstance.h>
//#include <clang/Frontend/CompilerInvocation.h>
#ifdef HAVE_BASIC_DIAGNOSTICOPTIONS_H
#include <clang/Basic/DiagnosticOptions.h>
#else
//#include <clang/Frontend/DiagnosticOptions.h>
#endif
//#include <clang/Frontend/TextDiagnosticPrinter.h>
#ifdef HAVE_LEX_HEADERSEARCHOPTIONS_H
#include <clang/Lex/HeaderSearchOptions.h>
#else
//#include <clang/Frontend/HeaderSearchOptions.h>
#endif
//#include <clang/Frontend/LangStandard.h>
#ifdef HAVE_LEX_PREPROCESSOROPTIONS_H
#include <clang/Lex/PreprocessorOptions.h>
#else
//#include <clang/Frontend/PreprocessorOptions.h>
#endif
//#include <clang/Frontend/FrontendOptions.h>
//#include <clang/Frontend/Utils.h>
#include <clang/Lex/HeaderSearch.h>
#include <clang/Lex/Preprocessor.h>
#include <clang/Lex/Pragma.h>
#include <clang/AST/ASTContext.h>
#include <clang/AST/ASTConsumer.h>
#include <clang/Sema/Sema.h>
#include <clang/Sema/SemaDiagnostic.h>
#include <clang/Parse/Parser.h>
#include <clang/Parse/ParseAST.h>

#include <isl/ctx.h>
#include <isl/constraint.h>

#include <pet.h>
#include "pet_cxx.h"
#include <fstream>

#include "scan.h"
#include "print.h"
#include "initialize_pet.h"

#define ARRAY_SIZE(array) (sizeof(array)/sizeof(*array))

using namespace std;
using namespace clang;
using namespace clang::driver;

#ifdef HAVE_ADT_OWNINGPTR_H
#define unique_ptr	llvm::OwningPtr
#endif

/* Called if we found something we didn't expect in one of the pragmas.
 * We'll provide more informative warnings later.
 */
static void unsupported(Preprocessor &PP, SourceLocation loc)
{
	DiagnosticsEngine &diag = PP.getDiagnostics();
	unsigned id = diag.getCustomDiagID(DiagnosticsEngine::Warning,
					   "unsupported");
	DiagnosticBuilder B = diag.Report(loc, id);
}

static int get_int(const char *s)
{
	return s[0] == '"' ? atoi(s + 1) : atoi(s);
}

static ValueDecl *get_value_decl(Sema &sema, Token &token)
{
	IdentifierInfo *name;
	Decl *decl;

	if (token.isNot(tok::identifier))
		return NULL;

	name = token.getIdentifierInfo();
	decl = sema.LookupSingleName(sema.TUScope, name,
				token.getLocation(), Sema::LookupOrdinaryName);
	return decl ? cast_or_null<ValueDecl>(decl) : NULL;
}

/* Handle pragmas of the form
 *
 *	#pragma value_bounds identifier lower_bound upper_bound
 *
 * For each such pragma, add a mapping
 *	{ identifier[] -> [i] : lower_bound <= i <= upper_bound }
 * to value_bounds.
 */
struct PragmaValueBoundsHandler : public PragmaHandler {
	Sema &sema;
	isl_ctx *ctx;
	isl_union_map *value_bounds;

	PragmaValueBoundsHandler(isl_ctx *ctx, Sema &sema) :
	    PragmaHandler("value_bounds"), ctx(ctx), sema(sema) {
		isl_space *space = isl_space_params_alloc(ctx, 0);
		value_bounds = isl_union_map_empty(space);
	}

	~PragmaValueBoundsHandler() {
		isl_union_map_free(value_bounds);
	}

	virtual void HandlePragma(Preprocessor &PP,
				  PragmaIntroducerKind Introducer,
				  Token &ScopTok) {
		isl_id *id;
		isl_space *dim;
		isl_map *map;
		ValueDecl *vd;
		Token token;
		int lb;
		int ub;

		PP.Lex(token);
		vd = get_value_decl(sema, token);
		if (!vd) {
			unsupported(PP, token.getLocation());
			return;
		}

		PP.Lex(token);
		if (!token.isLiteral()) {
			unsupported(PP, token.getLocation());
			return;
		}

		lb = get_int(token.getLiteralData());

		PP.Lex(token);
		if (!token.isLiteral()) {
			unsupported(PP, token.getLocation());
			return;
		}

		ub = get_int(token.getLiteralData());

		dim = isl_space_alloc(ctx, 0, 0, 1);
		map = isl_map_universe(dim);
		map = isl_map_lower_bound_si(map, isl_dim_out, 0, lb);
		map = isl_map_upper_bound_si(map, isl_dim_out, 0, ub);
		id = isl_id_alloc(ctx, vd->getName().str().c_str(), vd);
		map = isl_map_set_tuple_id(map, isl_dim_in, id);

		value_bounds = isl_union_map_add_map(value_bounds, map);
	}
};

/* Given a variable declaration, check if it has an integer initializer
 * and if so, add a parameter corresponding to the variable to "value"
 * with its value fixed to the integer initializer and return the result.
 */
static __isl_give isl_set *extract_initialization(__isl_take isl_set *value,
	ValueDecl *decl)
{
	VarDecl *vd;
	Expr *expr;
	IntegerLiteral *il;
	isl_val *v;
	isl_ctx *ctx;
	isl_id *id;
	isl_space *space;
	isl_set *set;

	vd = cast<VarDecl>(decl);
	if (!vd)
		return value;
	if (!vd->getType()->isIntegerType())
		return value;
	expr = vd->getInit();
	if (!expr)
		return value;
	il = cast<IntegerLiteral>(expr);
	if (!il)
		return value;

	ctx = isl_set_get_ctx(value);
	id = isl_id_alloc(ctx, vd->getName().str().c_str(), vd);
	space = isl_space_params_alloc(ctx, 1);
	space = isl_space_set_dim_id(space, isl_dim_param, 0, id);
	set = isl_set_universe(space);

	v = PetScan::extract_int(ctx, il);
	set = isl_set_fix_val(set, isl_dim_param, 0, v);

	return isl_set_intersect(value, set);
}

/* Handle pragmas of the form
 *
 *	#pragma parameter identifier lower_bound
 * and
 *	#pragma parameter identifier lower_bound upper_bound
 *
 * For each such pragma, intersect the context with the set
 * [identifier] -> { [] : lower_bound <= identifier <= upper_bound }
 */
struct PragmaParameterHandler : public PragmaHandler {
	Sema &sema;
	isl_set *&context;
	isl_set *&context_value;

	PragmaParameterHandler(Sema &sema, isl_set *&context,
		isl_set *&context_value) :
		PragmaHandler("parameter"), sema(sema), context(context),
		context_value(context_value) {}

	virtual void HandlePragma(Preprocessor &PP,
				  PragmaIntroducerKind Introducer,
				  Token &ScopTok) {
		isl_id *id;
		isl_ctx *ctx = isl_set_get_ctx(context);
		isl_space *dim;
		isl_set *set;
		ValueDecl *vd;
		Token token;
		int lb;
		int ub;
		bool has_ub = false;

		PP.Lex(token);
		vd = get_value_decl(sema, token);
		if (!vd) {
			unsupported(PP, token.getLocation());
			return;
		}

		PP.Lex(token);
		if (!token.isLiteral()) {
			unsupported(PP, token.getLocation());
			return;
		}

		lb = get_int(token.getLiteralData());

		PP.Lex(token);
		if (token.isLiteral()) {
			has_ub = true;
			ub = get_int(token.getLiteralData());
		} else if (token.isNot(tok::eod)) {
			unsupported(PP, token.getLocation());
			return;
		}

		id = isl_id_alloc(ctx, vd->getName().str().c_str(), vd);
		dim = isl_space_params_alloc(ctx, 1);
		dim = isl_space_set_dim_id(dim, isl_dim_param, 0, id);

		set = isl_set_universe(dim);

		set = isl_set_lower_bound_si(set, isl_dim_param, 0, lb);
		if (has_ub)
			set = isl_set_upper_bound_si(set, isl_dim_param, 0, ub);

		context = isl_set_intersect(context, set);

		context_value = extract_initialization(context_value, vd);
	}
};

/* Handle pragmas of the form
 *
 *	#pragma pencil independent
 *
 * For each such pragma, add an entry to the "independent" vector.
 */
struct PragmaPencilHandler : public PragmaHandler {
	std::vector<Independent> &independent;

	PragmaPencilHandler(std::vector<Independent> &independent) :
		PragmaHandler("pencil"), independent(independent) {}

	virtual void HandlePragma(Preprocessor &PP,
				  PragmaIntroducerKind Introducer,
				  Token &PencilTok) {
		Token token;
		IdentifierInfo *info;

		PP.Lex(token);
		if (token.isNot(tok::identifier))
			return;

		info = token.getIdentifierInfo();
		if (!info->isStr("independent"))
			return;

		PP.Lex(token);
		if (token.isNot(tok::eod))
			return;

		SourceManager &SM = PP.getSourceManager();
		SourceLocation sloc = PencilTok.getLocation();
		unsigned line = SM.getExpansionLineNumber(sloc);
		independent.push_back(Independent(line));
	}
};

#ifdef HAVE_TRANSLATELINECOL

/* Return a SourceLocation for line "line", column "col" of file "FID".
 */
SourceLocation translateLineCol(SourceManager &SM, FileID FID, unsigned line,
	unsigned col)
{
	return SM.translateLineCol(FID, line, col);
}

#else

/* Return a SourceLocation for line "line", column "col" of file "FID".
 */
SourceLocation translateLineCol(SourceManager &SM, FileID FID, unsigned line,
	unsigned col)
{
	return SM.getLocation(SM.getFileEntryForID(FID), line, col);
}

#endif

/* List of pairs of #pragma scop and #pragma endscop locations.
 */
struct ScopLocList {
	std::vector<ScopLoc> list;

	/* Add a new start (#pragma scop) location to the list.
	 * If the last #pragma scop did not have a matching
	 * #pragma endscop then overwrite it.
	 */
	void add_start(unsigned line, unsigned start) {
		ScopLoc loc;

		loc.start_line = line;
		loc.start = start;
		if (list.size() == 0 || list[list.size() - 1].end != 0)
			list.push_back(loc);
		else
			list[list.size() - 1] = loc;
	}

	/* Set the end location (#pragma endscop) of the last pair
	 * in the list.
	 * If there is no such pair of if the end of that pair
	 * is already set, then ignore the spurious #pragma endscop.
	 */
	void add_end(unsigned end) {
		if (list.size() == 0 || list[list.size() - 1].end != 0)
			return;
		list[list.size() - 1].end = end;
	}
};

/* Handle pragmas of the form
 *
 *	#pragma scop
 *
 * In particular, store the location of the line containing
 * the pragma in the list "scops".
 */
struct PragmaScopHandler : public PragmaHandler {
	ScopLocList &scops;

	PragmaScopHandler(ScopLocList &scops) :
		PragmaHandler("scop"), scops(scops) {}

	virtual void HandlePragma(Preprocessor &PP,
				  PragmaIntroducerKind Introducer,
				  Token &ScopTok) {
		SourceManager &SM = PP.getSourceManager();
		SourceLocation sloc = ScopTok.getLocation();
		int line = SM.getExpansionLineNumber(sloc);
		sloc = translateLineCol(SM, SM.getFileID(sloc), line, 1);
		scops.add_start(line, SM.getFileOffset(sloc));
	}
};

/* Handle pragmas of the form
 *
 *	#pragma endscop
 *
 * In particular, store the location of the line following the one containing
 * the pragma in the list "scops".
 */
struct PragmaEndScopHandler : public PragmaHandler {
	ScopLocList &scops;

	PragmaEndScopHandler(ScopLocList &scops) :
		PragmaHandler("endscop"), scops(scops) {}

	virtual void HandlePragma(Preprocessor &PP,
				  PragmaIntroducerKind Introducer,
				  Token &EndScopTok) {
		SourceManager &SM = PP.getSourceManager();
		SourceLocation sloc = EndScopTok.getLocation();
		int line = SM.getExpansionLineNumber(sloc);
		sloc = translateLineCol(SM, SM.getFileID(sloc), line + 1, 1);
		scops.add_end(SM.getFileOffset(sloc));
	}
};

/* Handle pragmas of the form
 *
 *	#pragma live-out identifier, identifier, ...
 *
 * Each identifier on the line is stored in live_out.
 */
struct PragmaLiveOutHandler : public PragmaHandler {
	Sema &sema;
	set<ValueDecl *> &live_out;

	PragmaLiveOutHandler(Sema &sema, set<ValueDecl *> &live_out) :
		PragmaHandler("live"), sema(sema), live_out(live_out) {}

	virtual void HandlePragma(Preprocessor &PP,
				  PragmaIntroducerKind Introducer,
				  Token &ScopTok) {
		Token token;

		PP.Lex(token);
		if (token.isNot(tok::minus))
			return;
		PP.Lex(token);
		if (token.isNot(tok::identifier) ||
		    !token.getIdentifierInfo()->isStr("out"))
			return;

		PP.Lex(token);
		while (token.isNot(tok::eod)) {
			ValueDecl *vd;

			vd = get_value_decl(sema, token);
			if (!vd) {
				unsupported(PP, token.getLocation());
				return;
			}
			live_out.insert(vd);
			PP.Lex(token);
			if (token.is(tok::comma))
				PP.Lex(token);
		}
	}
};

/* For each array in "scop", set its value_bounds property
 * based on the infofrmation in "value_bounds" and
 * mark it as live_out if it appears in "live_out".
 */
static void update_arrays(struct pet_scop *scop,
	__isl_take isl_union_map *value_bounds, set<ValueDecl *> &live_out)
{
	set<ValueDecl *>::iterator lo_it;
	isl_ctx *ctx = isl_union_map_get_ctx(value_bounds);

	if (!scop) {
		isl_union_map_free(value_bounds);
		return;
	}

	for (int i = 0; i < scop->n_array; ++i) {
		isl_id *id;
		isl_space *space;
		isl_map *bounds;
		ValueDecl *decl;
		pet_array *array = scop->arrays[i];

		id = isl_set_get_tuple_id(array->extent);
		decl = (ValueDecl *)isl_id_get_user(id);

		space = isl_space_alloc(ctx, 0, 0, 1);
		space = isl_space_set_tuple_id(space, isl_dim_in, id);

		bounds = isl_union_map_extract_map(value_bounds, space);
		if (!isl_map_plain_is_empty(bounds))
			array->value_bounds = isl_map_range(bounds);
		else
			isl_map_free(bounds);

		lo_it = live_out.find(decl);
		if (lo_it != live_out.end())
			array->live_out = 1;
	}

	isl_union_map_free(value_bounds);
}

/* Extract a pet_scop (if any) from each appropriate function.
 * Each detected scop is passed to "fn".
 * When autodetecting, at most one scop is extracted from each function.
 * If "function" is not NULL, then we only extract a pet_scop if the
 * name of the function matches.
 * If "autodetect" is false, then we only extract if we have seen
 * scop and endscop pragmas and if these are situated inside the function
 * body.
 */
struct PetASTConsumer : public ASTConsumer {
	ASTContext &ast_context;
	DiagnosticsEngine &diags;
	ScopLocList &scops;
	std::vector<Independent> independent;
	const char *function;
	pet_options *options;
	isl_ctx *ctx;
	isl_set *context;
	isl_set *context_value;
	set<ValueDecl *> live_out;
	int (*fn)(struct pet_scop *scop, void *user);
	void *user;
	bool error;
	isl_union_map *value_bounds;

	PetASTConsumer(isl_ctx *ctx, ASTContext &ast_context,
		DiagnosticsEngine &diags, ScopLocList &scops,
		const char *function, pet_options *options,
		int (*fn)(struct pet_scop *scop, void *user), void *user) :
		ctx(ctx), ast_context(ast_context), diags(diags),
		scops(scops), function(function), options(options),
		fn(fn), user(user), error(false)
	{
		isl_space *space;
		space = isl_space_params_alloc(ctx, 0);
		context = isl_set_universe(isl_space_copy(space));
		context_value = isl_set_universe(space);

		{
		  isl_space *space = isl_space_params_alloc(ctx, 0);
		  value_bounds = isl_union_map_empty(space);
		}
	}

	~PetASTConsumer() {
		isl_set_free(context);
		isl_set_free(context_value);
	}

	__isl_give isl_union_map *get_value_bounds() {
		return isl_union_map_copy(value_bounds);
	}

	/* Pass "scop" to "fn" after performing some postprocessing.
	 * In particular, add the context and value_bounds constraints
	 * speficied through pragmas, add reference identifiers and
	 * reset user pointers on parameters and tuple ids.
	 *
	 * If "scop" does not contain any statements and autodetect
	 * is turned on, then skip it.
	 */
	void call_fn(pet_scop *scop) {
		std::cout << "in call_fn" << endl;
		if (!scop)
			return;
		if (diags.hasErrorOccurred()) {
			pet_scop_free(scop);
			return;
		}
		if (options->autodetect && scop->n_stmt == 0) {
			pet_scop_free(scop);
			return;
		}
		std::cout << "in " << __LINE__ << endl;
		scop->context = isl_set_intersect(scop->context,
						isl_set_copy(context));
		scop->context_value = isl_set_intersect(scop->context_value,
						isl_set_copy(context_value));

		std::cout << "in " << __LINE__ << endl;
		update_arrays(scop, get_value_bounds(), live_out);
		std::cout << "in " << __LINE__ << endl;

		scop = pet_scop_add_ref_ids(scop);
		scop = pet_scop_anonymize(scop);
		std::cout << "in " << __LINE__ << endl;

		if (fn(scop, user) < 0)
			error = true;
		std::cout << "leaving call_fn" << endl;
	}

#if 0
	void scan_stmt( ForStmt*  ) {
	  pet_scop *scop;

	  // location of this statement 
	  ScopLoc loc = scops.list.front();
	  isl_union_map *vb = value_bounds;
	  PetScan ps( ast_context, loc, options,
	    isl_union_map_copy(vb), independent);
	  scop = ps.scan( stmt );
	  call_fn( scop );
	}
#endif

	/* For each explicitly marked scop (using pragmas),
	 * extract the scop and call "fn" on it if it is inside "fd".
	 */
	void scan_scops(FunctionDecl *fd, std::unique_ptr<std::map<std::string,std::string>>& call_texts ) {
		unsigned start, end;
		vector<ScopLoc>::iterator it;
		isl_union_map *vb = value_bounds;
		SourceManager &SM = ast_context.getSourceManager();
		pet_scop *scop;

		if (scops.list.size() == 0)
			return;

		start = SM.getFileOffset(fd->getLocStart());
		end = SM.getFileOffset(fd->getLocEnd());

		for (it = scops.list.begin(); it != scops.list.end(); ++it) {
			ScopLoc loc = *it;
			if (!loc.end)
				continue;
			if (start > loc.end)
				continue;
			if (end < loc.start)
				continue;
			PetScan ps( ast_context, loc, options,
				    isl_union_map_copy(vb), independent);
			scop = ps.scan(fd);
			call_fn(scop);
			if ( scop ) {
			  call_texts.reset(ps.name_to_text.release());
			}
		}
	}

#if 0
	virtual HandleTopLevelDeclReturn HandleTopLevelDecl(DeclGroupRef dg) {

		std::cout << "in HandleTopLevelDecl " << endl;

		if (error)
			return HandleTopLevelDeclContinue;

		for (auto it = dg.begin(); it != dg.end(); ++it) {
		        std::cout << "in for loop" << endl;
			isl_union_map *vb = value_bounds;
		        std::cout << "after vb" << endl;
			FunctionDecl *fd = dyn_cast<clang::FunctionDecl>(*it);
		        std::cout << "after fd cast" << endl;
			if (!fd)
				continue;
			if (!fd->hasBody())
				continue;
			if (function &&
			    fd->getNameInfo().getAsString() != function)
				continue;
			if (options->autodetect) {
				ScopLoc loc;
				pet_scop *scop;
				std::cout << "starting autodetect" << endl;
				PetScan ps(PP, ast_context, loc, options,
					    isl_union_map_copy(vb),
					    independent);
				std::cout << "after creation" << endl;
				scop = ps.scan(fd);
				std::cout << "after scan" << endl;
				call_fn(scop);
				continue;
			}
		        std::cout << "before scan scop" << endl;
			scan_scops(fd);
		}

		std::cout << "returning from HandleTopLevelDecl" << endl;
		return HandleTopLevelDeclContinue;
	}
#endif
};



/* Store "scop" into the address pointed to by "user".
 * Return -1 to indicate that we are not interested in any further scops.
 * This function should therefore not be called a second call
 * so in principle there is no need to check if we have already set *user.
 */
static int set_first_scop(pet_scop *scop, void *user)
{
	pet_scop **p = (pet_scop **) user;

	if (!*p)
		*p = scop;
	else
		pet_scop_free(scop);

	return -1;
}


// TODO make it take arguments wether to autodetect or not
Pet::Pet( 
				  clang::DiagnosticsEngine& _diags,
				  clang::ASTContext* clang_ctx
      ) :
      scops( new ScopLocList ),
      diags(&_diags)
{
  std::cout << __PRETTY_FUNCTION__ << std::endl;
}


Pet::~Pet() {
  std::cout << __PRETTY_FUNCTION__ << std::endl;
  if ( consumer ) delete consumer;
  if ( scops ) delete scops;
  std::cout << "done " << __PRETTY_FUNCTION__ << std::endl;
}


void Pet::initialize_consumer( clang::ASTContext* clang_ctx ) {
  std::cout << __PRETTY_FUNCTION__ << std::endl;
  const char* function = nullptr;

  pet_options* options = nullptr; // = isl_ctx_peek_pet_options(ctx);
  if (!options) {
    std::cout << "no options found allocating defaults" << std::endl;
    int argc = 1;
    char* argv[1] = { "pet_cxx" };
    ctx = initialize_pet_options( 1 , argv ); 
    options = isl_ctx_peek_pet_options(ctx);
    assert( options && "options are not present but should be" );
    //options = pet_options_new_with_defaults();
    //ctx = isl_ctx_alloc_with_options(nullptr, options);
    
    std::cout << "done allocating defaults" << std::endl;
  }

  std::cout << "before create consumer" << endl;
  consumer = new PetASTConsumer(ctx, *clang_ctx, *diags,
			*scops, function, options, &set_first_scop, &scop );
  std::cout << "after create consumer" << endl;

  consumer_initialized = true;
}


void Pet::pet_scop_extract_from_clang_ast( 
				      clang::ASTContext* clang_ctx,
				      clang::ForStmt* stmt,
				      clang::FunctionDecl* fd,
				      std::unique_ptr<std::map<std::string,std::string>>& call_texts,
				      pet_scop** _scop
				    ){


  SourceManager& SM = clang_ctx->getSourceManager();
  // fill the scop loc list with the information about this loop
  // first clear the list 
  scops->list.clear();

  // for the start of the statement
  {
    SourceLocation sloc = stmt->getLocStart();
    int line = SM.getExpansionLineNumber(sloc);
    sloc = translateLineCol(SM, SM.getFileID(sloc), line, 1);
    scops->add_start(line, SM.getFileOffset(sloc));
  }
  // for the end of the statement
  {
    SourceLocation sloc = stmt->getLocEnd();
    int line = SM.getExpansionLineNumber(sloc);
    sloc = translateLineCol(SM, SM.getFileID(sloc), line + 1, 1);
    scops->add_end(SM.getFileOffset(sloc));
  }


  if ( consumer_initialized == false ) {
    std::cout << "initializing consumer" << std::endl;
    initialize_consumer( clang_ctx ); 
   }

#if 0
  // braces are needed for the build object to be destroyed
  {
    auto& element = stmt;
    auto loc = element->getLocStart();
    DiagnosticsEngine &diag = clang_ctx->getDiagnostics();
    unsigned id = diag.getCustomDiagID(DiagnosticsEngine::Warning,
				       "test diagnostic");
    diag.Report(loc, id);
  }
#endif
  
  consumer->scan_scops( fd, call_texts );

#if 0
  std::cout << "before htd" << endl;
  consumer->HandleTopLevelDecl(dg);
  std::cout << "after htd" << endl;
#endif

  if ( scop ) {
    std::cout << "found a scop" << endl;
  }
  *_scop = scop;

  // reset for next dg
  scop = nullptr;
}











