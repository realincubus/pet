/*
 * Copyright 2011      Leiden University. All rights reserved.
 * Copyright 2012-2015 Ecole Normale Superieure. All rights reserved.
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

//#include "config.h"

#include <string.h>
#include <set>
#include <map>
#include <iostream>
#include <llvm/Support/raw_ostream.h>
#include <clang/AST/ASTContext.h>
#include <clang/AST/ASTDiagnostic.h>
#include <clang/AST/Attr.h>
#include <clang/AST/Expr.h>
#include <clang/AST/RecursiveASTVisitor.h>
#include <clang/AST/StmtIterator.h>

#include <isl/id.h>
#include <isl/space.h>
#include <isl/aff.h>
#include <isl/set.h>
#include <isl/union_set.h>

#include "aff.h"
#include "array.h"
#include "clang.h"
#include "context.h"
#include "expr.h"
#include "nest.h"
#include "options.h"
#include "scan.h"
#include "scop.h"
#include "scop_plus.h"
#include "tree.h"
#include "tree2scop.h"

#include "isl_type_information.h"

using namespace std;
using namespace clang;


static Expr* ignoreImplicitCast( Expr* e ) {
	if ( auto ice = dyn_cast_or_null<ImplicitCastExpr>( e ) ) {
		cerr << "is implicit cast" << endl;
		return ice->getSubExpr();
	}
	return e;
}
//static bool isStdContainerIteratorCreator( std::string name );
//static DeclRefExpr* build_base_expression_by_initializer( Expr* e ) ;
//static DeclRefExpr* build_index_expression_by_decl( Expr* e );

static enum pet_op_type UnaryOperatorKind2pet_op_type(UnaryOperatorKind kind)
{
        cerr << __PRETTY_FUNCTION__ << " kind is "  << kind << endl;
	switch (kind) {
	case UO_Minus:
		return pet_op_minus;
	case UO_Not:
		return pet_op_not;
	case UO_LNot:
		return pet_op_lnot;
	case UO_PostInc:
		return pet_op_post_inc;
	case UO_PostDec:
		return pet_op_post_dec;
	case UO_PreInc:
		return pet_op_pre_inc;
	case UO_PreDec:
		return pet_op_pre_dec;
        case UO_Deref:
                return pet_op_deref;
	default:
		return pet_op_last;
	}
}

static enum pet_op_type BinaryOperatorKind2pet_op_type(BinaryOperatorKind kind)
{
	switch (kind) {
	case BO_AddAssign:
		return pet_op_add_assign;
	case BO_SubAssign:
		return pet_op_sub_assign;
	case BO_MulAssign:
		return pet_op_mul_assign;
	case BO_DivAssign:
		return pet_op_div_assign;
	case BO_Assign:
		return pet_op_assign;
	case BO_Add:
		return pet_op_add;
	case BO_Sub:
		return pet_op_sub;
	case BO_Mul:
		return pet_op_mul;
	case BO_Div:
		return pet_op_div;
	case BO_Rem:
		return pet_op_mod;
	case BO_Shl:
		return pet_op_shl;
	case BO_Shr:
		return pet_op_shr;
	case BO_EQ:
		return pet_op_eq;
	case BO_NE:
		return pet_op_ne;
	case BO_LE:
		return pet_op_le;
	case BO_GE:
		return pet_op_ge;
	case BO_LT:
		return pet_op_lt;
	case BO_GT:
		return pet_op_gt;
	case BO_And:
		return pet_op_and;
	case BO_Xor:
		return pet_op_xor;
	case BO_Or:
		return pet_op_or;
	case BO_LAnd:
		return pet_op_land;
	case BO_LOr:
		return pet_op_lor;
	default:
		return pet_op_last;
	}
}


// these types can be obtained from 
// clang/Basic/OperatorKinds.def
// TODO fill in the right translation from ook to pet kind
static enum pet_op_type OverloadedOperatorKind2pet_op_type(OverloadedOperatorKind kind)
{
	switch (kind) {
#if 0
	case BO_AddAssign:
		return pet_op_add_assign;
	case BO_SubAssign:
		return pet_op_sub_assign;
	case BO_MulAssign:
		return pet_op_mul_assign;
	case BO_DivAssign:
		return pet_op_div_assign;
#endif
	case OO_Equal:
		return pet_op_assign;
	case OO_Less:
		return pet_op_lt;
	case OO_PlusPlus:
		return pet_op_post_inc;
	case OO_LessLess:
		return pet_op_shl;
#if 0
	case BO_Add:
		return pet_op_add;
	case BO_Sub:
		return pet_op_sub;
	case BO_Mul:
		return pet_op_mul;
	case BO_Div:
		return pet_op_div;
	case BO_Rem:
		return pet_op_mod;
	case BO_Shl:
		return pet_op_shl;
	case BO_Shr:
		return pet_op_shr;
	case BO_EQ:
		return pet_op_eq;
	case BO_NE:
		return pet_op_ne;
	case BO_LE:
		return pet_op_le;
	case BO_GE:
		return pet_op_ge;
	case BO_LT:
		return pet_op_lt;
	case BO_GT:
		return pet_op_gt;
	case BO_And:
		return pet_op_and;
	case BO_Xor:
		return pet_op_xor;
	case BO_Or:
		return pet_op_or;
	case BO_LAnd:
		return pet_op_land;
	case BO_LOr:
		return pet_op_lor;
#endif
	// NOTE : pet has no idea about the star operator 
	//        if its not in this list a client function maybe has to 
	//        deal with the OO type
	default:
		return pet_op_last;
	}
}

#if 1
static DeclRefExpr *create_DeclRefExpr(VarDecl *var)
{
	return DeclRefExpr::Create(var->getASTContext(), var->getQualifierLoc(),
		SourceLocation(), var, false, var->getInnerLocStart(),
		var->getType(), VK_LValue);
}
#elif defined(DECLREFEXPR_CREATE_REQUIRES_SOURCELOCATION)
static DeclRefExpr *create_DeclRefExpr(VarDecl *var)
{
	return DeclRefExpr::Create(var->getASTContext(), var->getQualifierLoc(),
		SourceLocation(), var, var->getInnerLocStart(), var->getType(),
		VK_LValue);
}
#else
static DeclRefExpr *create_DeclRefExpr(VarDecl *var)
{
	return DeclRefExpr::Create(var->getASTContext(), var->getQualifierLoc(),
		var, var->getInnerLocStart(), var->getType(), VK_LValue);
}
#endif

static VarDecl *create_VarDecl(VarDecl* var, ASTContext* ctx)
{
	// ASTContext &C, 
	// DeclContext *DC, 
	// SourceLocation StartLoc, 
	// SourceLocation IdLoc, 
	// IdentifierInfo *Id, 
	// QualType T, 
	// TypeSourceInfo *TInfo, 
	// StorageClass S
	BuiltinType* bit = new BuiltinType( BuiltinType::Int );
	QualType q( bit, 0 );
	auto tsi = ctx->CreateTypeSourceInfo( q );
	
	return VarDecl::Create(
			var->getASTContext(),
			var->getDeclContext(), 
			var->getInnerLocStart(), 
			var->getInnerLocStart(), 
			var->getIdentifier(),
			q, 
			tsi,
			var->getStorageClass()
			);
}

#if 1

static int size_in_bytes(ASTContext &context, QualType type)
{
	return context.getTypeInfo(type).Width / 8;
}

#else

static int size_in_bytes(ASTContext &context, QualType type)
{
	return context.getTypeInfo(type).first / 8;
}

#endif

/* Check if the element type corresponding to the given array type
 * has a const qualifier.
 */
static bool const_base(QualType qt)
{
	const Type *type = qt.getTypePtr();

	if (type->isPointerType())
		return const_base(type->getPointeeType());
	if (type->isArrayType()) {
		const ArrayType *atype;
		type = type->getCanonicalTypeInternal().getTypePtr();
		atype = cast<ArrayType>(type);
		return const_base(atype->getElementType());
	}

	return qt.isConstQualified();
}


static bool isShadowing( NamedDecl* decl, DeclContext* dc ) {

  //std::cerr << "lookup for this decl:" << std::endl;
  //decl->dump();
  //std::cerr << "decl contexts" << std::endl;
  //dc->dumpDeclContext();
  //std::cerr << "lookups" << std::endl;
  //dc->dumpLookups();

  auto name = decl->getDeclName();
  auto lookup_results = dc->noload_lookup( name );

  std::cerr << __PRETTY_FUNCTION__ << " results " << lookup_results.size() << std::endl;
  for( auto& lookup_result : lookup_results ){
    std::cerr << "decl " << decl->getName().str() << " is shadowing :" << std::endl;
    lookup_result->dump(); 
    std::cerr << std::endl;  
  }

  // recurse until you find something
  if ( lookup_results.size() == 0 ) {
    if ( auto parent = dc->getLookupParent() ){
      return isShadowing( decl, parent ); 
    }else{
      return false;
    }
  }
  return true;
}

/* Create an isl_id that refers to the named declarator "decl".
 */
static __isl_give isl_id *create_decl_id(isl_ctx *ctx, NamedDecl *decl)
{
  cerr << __PRETTY_FUNCTION__ << endl;
  auto *dc = decl->getDeclContext();
  if ( isShadowing( decl, dc ) ) {
    std::cerr << "decl " << decl->getName().str() << " is shadowing " << std::endl;
  }
  cerr << "new id with name: " << decl->getName().str() << endl;
  if ( auto value_decl = dyn_cast_or_null<ValueDecl>( decl ) ) {
	  cerr  << " and type " << value_decl->getType().getAsString() << endl;
  }
  // TODO extra logic for references to reference variables
  if ( auto value_decl = dyn_cast_or_null<ValueDecl>( decl ) ) {
    // get the type 
    if ( auto type = value_decl->getType().getTypePtr() ) {
      if ( type->isReferenceType() ){
	cerr << "is a reference type so create a decl to its left hand side of initialization ? " << endl;
	// better direct the analysis to follow to the left hande side;
      }else{
	cerr << "is not a refrence type" << endl;
	type->dump();
      }
    }
  }


  return isl_id_alloc(ctx, decl->getName().str().c_str(), register_user_data_type((void*)decl, ITI_NamedDecl) );
}

PetScan::~PetScan()
{
	std::map<const Type *, pet_expr *>::iterator it;
	std::map<FunctionDecl *, pet_function_summary *>::iterator it_s;

	for (it = type_size.begin(); it != type_size.end(); ++it)
		pet_expr_free(it->second);
	for (it_s = summary_cache.begin(); it_s != summary_cache.end(); ++it_s)
		pet_function_summary_free(it_s->second);

	isl_union_map_free(value_bounds);
}

DiagnosticsEngine& PetScan::getDiagnostics() {
  assert( diagnosticsEngine && "diagnostics engine is not set" );
  return ast_context.getDiagnostics(); 
  //return *diagnosticsEngine;
}

/* Report a diagnostic, unless autodetect is set.
 */
void PetScan::report(Stmt *stmt, unsigned id, std::string debug_information )
{
	if (options->autodetect)
		return;

	std::cerr << "in " << __PRETTY_FUNCTION__ << std::endl;
	SourceLocation loc = stmt->getLocStart();
	std::cerr << "got loc " << __PRETTY_FUNCTION__ << std::endl;
	DiagnosticsEngine &diag = getDiagnostics();
	std::cerr << "got diag engine " << __PRETTY_FUNCTION__ << std::endl;
	DiagnosticBuilder B = diag.Report(loc, id) << debug_information << stmt->getSourceRange() ;
	std::cerr << "done reporting " << __PRETTY_FUNCTION__ << std::endl;
}

/* Called if we found something we (currently) cannot handle.
 * We'll provide more informative warnings later.
 *
 * We only actually complain if autodetect is false.
 */
void PetScan::unsupported(Stmt *stmt)
{
	DiagnosticsEngine &diag = getDiagnostics();
	unsigned id = diag.getCustomDiagID(DiagnosticsEngine::Warning,
					   "unsupported");
	report(stmt, id);
}

/* Called if we found something we (currently) cannot handle.
 * We'll provide more informative warnings later.
 *
 * We only actually complain if autodetect is false.
 */
void PetScan::unsupported_with_extra_string(Stmt *stmt, std::string extra)
{
	DiagnosticsEngine &diag = getDiagnostics();
	unsigned id = diag.getCustomDiagID(DiagnosticsEngine::Warning,
					   "unsupported by pet: %0" );
	report(stmt, id, extra );
}

#define unsupported( x ) unsupported_with_extra_string( (x), string(__FILE__) + string(" ") + to_string(__LINE__) )
#define unsupported_msg( x, y ) unsupported_with_extra_string( (x), string(__FILE__) + string(" ") + to_string(__LINE__) + string(" ") + y )
//#define unsupported_msg( x, y ) unsupported( (x) )


/* Called if we found somthing that might be a problem
 * We simply assume the best
 */
void PetScan::warning_assume_with_extra_string(Stmt *stmt, std::string extra)
{
  std::cerr << __PRETTY_FUNCTION__ << std::endl;
  DiagnosticsEngine &diag = getDiagnostics();
  std::cerr << "diag id" << std::endl;
  unsigned id = diag.getCustomDiagID(DiagnosticsEngine::Warning,
				     "Assumption by Pet: %0" );
  std::cerr << "reporting to " << id << " " << extra << " at " << stmt << std::endl;
  report(stmt, id, extra );
  std::cerr << "done reporting" << std::endl;
}

#define warning_assume( x, y ) warning_assume_with_extra_string( (x), string(__FILE__) + string(" ") + to_string(__LINE__) + string(" ") + y )

/* Called if we found somthing the user might be interested in
 */
void PetScan::note_understood_with_extra_string(Stmt *stmt, std::string extra)
{
	DiagnosticsEngine &diag = getDiagnostics();
	unsigned id = diag.getCustomDiagID(DiagnosticsEngine::Warning,
					   "Understood by Pet: %0" );
	report(stmt, id, extra );
}

// TODO since this is not printed i need to use the warning level to get some information
//      when ycm starts to print notes swtich to DiasgnosticsEnginine::Note
#define note_understood( x, y ) note_understood_with_extra_string( (x), string(__FILE__) + string(" ") + to_string(__LINE__) + string(" ") + y )

#if 0
/* Report an unsupported statement type, unless autodetect is set.
 */
void PetScan::report_unsupported_statement_type(Stmt *stmt)
{
	DiagnosticsEngine &diag = getDiagnostics();
	unsigned id = diag.getCustomDiagID(DiagnosticsEngine::Warning,
				   "this type of statement is not supported");
	report(stmt, id);
}
#endif

void PetScan::report_unsupported_statement_type_with_extra_string(Stmt *stmt, std::string extra )
{
	DiagnosticsEngine &diag = getDiagnostics();
	unsigned id = diag.getCustomDiagID(DiagnosticsEngine::Warning,
				   "this type of statement is not supported");
	report(stmt, id, extra );
}

#define report_unsupported_statement_type( x ) report_unsupported_statement_type_with_extra_string( (x), string(__FILE__) + string(" ") + to_string(__LINE__) + string(" ") )

/* Report a missing prototype, unless autodetect is set.
 */
void PetScan::report_prototype_required(Stmt *stmt)
{
	DiagnosticsEngine &diag = getDiagnostics();
	unsigned id = diag.getCustomDiagID(DiagnosticsEngine::Warning,
					   "prototype required");
	report(stmt, id);
}

/* Report a missing increment, unless autodetect is set.
 */
void PetScan::report_missing_increment(Stmt *stmt)
{
	DiagnosticsEngine &diag = getDiagnostics();
	unsigned id = diag.getCustomDiagID(DiagnosticsEngine::Warning,
					   "missing increment");
	report(stmt, id);
}

/* Report a missing summary function, unless autodetect is set.
 */
void PetScan::report_missing_summary_function(Stmt *stmt)
{
	DiagnosticsEngine &diag = getDiagnostics();
	unsigned id = diag.getCustomDiagID(DiagnosticsEngine::Warning,
					   "missing summary function");
	report(stmt, id);
}

/* Report a missing summary function body, unless autodetect is set.
 */
void PetScan::report_missing_summary_function_body(Stmt *stmt)
{
	DiagnosticsEngine &diag = getDiagnostics();
	unsigned id = diag.getCustomDiagID(DiagnosticsEngine::Warning,
					   "missing summary function body");
	report(stmt, id);
}

/* Extract an integer from "val", which is assumed to be non-negative.
 */
static __isl_give isl_val *extract_unsigned(isl_ctx *ctx,
	const llvm::APInt &val)
{
	unsigned n;
	const uint64_t *data;

	data = val.getRawData();
	n = val.getNumWords();
	return isl_val_int_from_chunks(ctx, n, sizeof(uint64_t), data);
}

/* Extract an integer from "val".  If "is_signed" is set, then "val"
 * is signed.  Otherwise it it unsigned.
 */
static __isl_give isl_val *extract_int(isl_ctx *ctx, bool is_signed,
	llvm::APInt val)
{
	int is_negative = is_signed && val.isNegative();
	isl_val *v;

	if (is_negative)
		val = -val;

	v = extract_unsigned(ctx, val);

	if (is_negative)
		v = isl_val_neg(v);
	return v;
}

/* Extract an integer from "expr".
 */
__isl_give isl_val *PetScan::extract_int(isl_ctx *ctx, IntegerLiteral *expr)
{
	const Type *type = expr->getType().getTypePtr();
	bool is_signed = type->hasSignedIntegerRepresentation();

	return ::extract_int(ctx, is_signed, expr->getValue());
}

/* Extract an integer from "expr".
 * Return NULL if "expr" does not (obviously) represent an integer.
 */
__isl_give isl_val *PetScan::extract_int(clang::ParenExpr *expr)
{
	return extract_int(expr->getSubExpr());
}

/* Extract an integer from "expr".
 * Return NULL if "expr" does not (obviously) represent an integer.
 */
__isl_give isl_val *PetScan::extract_int(clang::Expr *expr)
{
	if (expr->getStmtClass() == Stmt::IntegerLiteralClass)
		return extract_int(ctx, cast<IntegerLiteral>(expr));
	if (expr->getStmtClass() == Stmt::ParenExprClass)
		return extract_int(cast<ParenExpr>(expr));

	unsupported(expr);
	return NULL;
}

/* Extract a pet_expr from the APInt "val", which is assumed
 * to be non-negative.
 */
__isl_give pet_expr *PetScan::extract_expr(const llvm::APInt &val)
{
	return pet_expr_new_int(extract_unsigned(ctx, val));
}

/* Return the number of bits needed to represent the type "qt",
 * if it is an integer type.  Otherwise return 0.
 * If qt is signed then return the opposite of the number of bits.
 */
int PetScan::get_type_size(QualType qt, ASTContext &ast_context)
{
	std::cerr << __PRETTY_FUNCTION__ << std::endl;
	int size;

	qt->dump();
	std::cerr << qt.getAsString() << std::endl;
	// TODO handle function proto types as well 

	if (!qt->isIntegerType() && !isIteratorType( qt.getTypePtr() ) ){
		cerr << "not an integer and not a iterator type" << endl;
		return 0;
	}

	size = ast_context.getIntWidth(qt);
	if (!qt->isUnsignedIntegerType())
		size = -size;

	std::cerr << "done " << __PRETTY_FUNCTION__ << " " << qt.getAsString() << " "  << size << std::endl;
	return size;
}

/* Return the number of bits needed to represent the type of "decl",
 * if it is an integer type.  Otherwise return 0.
 * If qt is signed then return the opposite of the number of bits.
 */
int PetScan::get_type_size(ValueDecl *decl)
{
	if ( FunctionDecl* fdecl = dyn_cast_or_null<FunctionDecl>( decl ) ){
		cerr << "getting type size for function " << endl;
		fdecl->dump();
	  return get_type_size(fdecl->getReturnType(),decl->getASTContext() );
	}
	
	return get_type_size(decl->getType(), decl->getASTContext());
}

/* Bound parameter "pos" of "set" to the possible values of "decl".
 */
__isl_give isl_set *PetScan::set_parameter_bounds(__isl_take isl_set *set,
	unsigned pos, ValueDecl *decl)
{
	int type_size;
	isl_ctx *ctx;
	isl_val *bound;

	ctx = isl_set_get_ctx(set);
	type_size = get_type_size(decl);
	if (type_size == 0)
		isl_die(ctx, isl_error_invalid, "not an integer type",
			return isl_set_free(set));
	if (type_size > 0) {
		set = isl_set_lower_bound_si(set, isl_dim_param, pos, 0);
		bound = isl_val_int_from_ui(ctx, type_size);
		bound = isl_val_2exp(bound);
		bound = isl_val_sub_ui(bound, 1);
		set = isl_set_upper_bound_val(set, isl_dim_param, pos, bound);
	} else {
		bound = isl_val_int_from_ui(ctx, -type_size - 1);
		bound = isl_val_2exp(bound);
		bound = isl_val_sub_ui(bound, 1);
		set = isl_set_upper_bound_val(set, isl_dim_param, pos,
						isl_val_copy(bound));
		bound = isl_val_neg(bound);
		bound = isl_val_sub_ui(bound, 1);
		set = isl_set_lower_bound_val(set, isl_dim_param, pos, bound);
	}

	return set;
}

__isl_give pet_expr *PetScan::extract_index_expr(ImplicitCastExpr *expr)
{
	return extract_index_expr(expr->getSubExpr());
}

static bool isRecordTypeByName( const Type* type_ptr, std::string name ) {
  // check for beeing a record type
  if ( !type_ptr->isRecordType() ) return false;

  // get the declaration 
  auto* record_type = type_ptr->getAs<RecordType>();
  if( auto* record_decl = record_type->getDecl() ) {
    if ( record_decl->getQualifiedNameAsString() == name ) return true;
  }

  return false;
}

static bool isSmartPointerToArray( const Type* type_ptr ) {
  // check for beeing a record type
  if ( !type_ptr->isRecordType() ) return false;

  // get the declaration 
  auto* record_type = type_ptr->getAs<RecordType>();
  if ( auto* record_decl = record_type->getDecl() ) {
    cerr  << __PRETTY_FUNCTION__ << endl;
    cerr  << "record is " << record_decl->getQualifiedNameAsString() << endl;
    if ( record_decl->getQualifiedNameAsString() == "std::unique_ptr" || record_decl->getQualifiedNameAsString() == "std::shared_ptr" ){
      return true;
    }
  }

  return false;
}

static bool isStdVector( QualType qt ) {
  return isRecordTypeByName( qt.getTypePtr(), "std::vector" );
}

static bool isStdArray( QualType qt ) {
  return isRecordTypeByName( qt.getTypePtr(), "std::array" );
}

static bool isRandomAccessStlType( const Type* type ) {
  return isRecordTypeByName( type, "std::array" ) || isRecordTypeByName( type, "std::vector" ) ||
         isRecordTypeByName( type, "std::__cxx11::basic_string" ) || isRecordTypeByName( type, "std::basic_string" ) ||
	        isRecordTypeByName( type, "std::deque" ) || isSmartPointerToArray( type );
}

static bool isRandomAccessStlType( QualType qt ) {
  auto type_ptr = qt.getTypePtr();
  return isRandomAccessStlType( type_ptr );
}

/* Return the depth of an array of the given type.
 */
static int array_depth(const Type *type)
{
	std::cerr << __PRETTY_FUNCTION__ << " " << type << std::endl;
	type->dump();

	// if it is a reference -> unwrap this one level
	if (type->isLValueReferenceType() ){
	  cerr << "is a l value reference type " << endl;
	  auto lvrt = dyn_cast_or_null<LValueReferenceType>( type );
	  if ( !lvrt ) {
	    std::cerr << "not implemented" << std::endl;
	    std::cerr << "handle this somehow" << std::endl;
	    exit(-1);
	  }
	  auto pt = lvrt->getPointeeType();
	  return array_depth( pt.getTypePtr() );
	}

	if (type->isPointerType())
		return 1 + array_depth(type->getPointeeType().getTypePtr());
	if (type->isArrayType()) {
		const ArrayType *atype;
		type = type->getCanonicalTypeInternal().getTypePtr();
		atype = cast<ArrayType>(type);
		return 1 + array_depth(atype->getElementType().getTypePtr());
	}

	// TODO not sure about that if ( isIteratorType( type ) ) return 1;

	// add support for c++ sequential memory types
	if ( const TemplateSpecializationType* tst = type->getAs<TemplateSpecializationType>() ){
	  std::cerr << "is a TemplateSpecializationType with args " << tst->getNumArgs() << std::endl;

	  // check for a std::vector 
	  if ( tst->getNumArgs() == 1 ) {
	    // TODO merge all together one argument types together
	    // get the record that belongs to this template
	    auto qual_type = tst->desugar();
	    if ( isStdVector( qual_type ) ) {
	      auto arg0 = tst->getArg(0);
	      auto qual_type = arg0.getAsType();
	      // recurse into the next level
	      return 1 + array_depth( qual_type.getTypePtr() ); 
	    }
	    if ( isRecordTypeByName( qual_type.getTypePtr(), "std::deque" ) ){
	      auto arg0 = tst->getArg(0);
	      auto qual_type = arg0.getAsType();
	      // recurse into the next level
	      return 1 + array_depth( qual_type.getTypePtr() ); 
	    }
	    if ( isRecordTypeByName( qual_type.getTypePtr(), "std::__cxx11::basic_string" ) ||  isRecordTypeByName( qual_type.getTypePtr(), "std::basic_string" ) ){
	      auto arg0 = tst->getArg(0);
	      auto qual_type = arg0.getAsType();
	      // recurse into the next level
	      return 1 + array_depth( qual_type.getTypePtr() ); 
	    }
      if ( isRecordTypeByName( qual_type.getTypePtr(), "std::unique_ptr" ) ){
        cerr << "is unique_ptr getting argument" << endl;
	      auto arg0 = tst->getArg(0);
	      auto qual_type = arg0.getAsType();
	      // recurse into the next level
	      return 1 + array_depth( qual_type.getTypePtr() ); 
      }
	  }

	  // check for a std::array
	  if ( tst->getNumArgs() == 2 ) {
	    // get the record that belongs to this template
	    auto qual_type = tst->desugar();
	    if ( isStdArray( qual_type ) ) {
	      auto arg0 = tst->getArg(0);
	      auto qual_type = arg0.getAsType();
	      // recurse into the next level
	      return 1 + array_depth( qual_type.getTypePtr() ); 
	    }
	  }
	}
	std::cerr << "done" << __PRETTY_FUNCTION__ << std::endl;
	return 0;
}

/* Return the depth of the array accessed by the index expression "index".
 * If "index" is an affine expression, i.e., if it does not access
 * any array, then return 1.
 * If "index" represent a member access, i.e., if its range is a wrapped
 * relation, then return the sum of the depth of the array of structures
 * and that of the member inside the structure.
 */
static int extract_depth(__isl_keep isl_multi_pw_aff *index)
{
	std::cerr << __PRETTY_FUNCTION__ << std::endl;
	isl_id *id;
	ValueDecl *decl;

	if (!index)
		return -1;

	if (isl_multi_pw_aff_range_is_wrapping(index)) {
		int domain_depth, range_depth;
		isl_multi_pw_aff *domain, *range;

		domain = isl_multi_pw_aff_copy(index);
		domain = isl_multi_pw_aff_range_factor_domain(domain);
		domain_depth = extract_depth(domain);
		isl_multi_pw_aff_free(domain);
		range = isl_multi_pw_aff_copy(index);
		range = isl_multi_pw_aff_range_factor_range(range);
		range_depth = extract_depth(range);
		isl_multi_pw_aff_free(range);

		return domain_depth + range_depth;
	}

	if (!isl_multi_pw_aff_has_tuple_id(index, isl_dim_out))
		return 1;

	id = isl_multi_pw_aff_get_tuple_id(index, isl_dim_out);
	if (!id)
		return -1;

	auto user_data = isl_id_get_user( id );
	// type lookup 
	auto type = get_isl_id_user_data_type( user_data );
  
	// TODO remove the ITI_Unknown
	if ( type == ITI_NamedDecl || type == ITI_Unknown ) {
	  std::cerr << __PRETTY_FUNCTION__ << " is a NamedDecl" << std::endl;
	  decl = (ValueDecl *) user_data;
	  isl_id_free(id);

	  return array_depth(decl->getType().getTypePtr());
	}

	if ( type == ITI_StringLiteral ) {
	  std::cerr << " is a string literal" << std::endl;
	  isl_id_free(id);

	  // string literals always have a depth of 1
	  return 1;
	}
}

/* Return the depth of the array accessed by the access expression "expr".
 */
static int extract_depth(__isl_keep pet_expr *expr)
{
  std::cerr << __PRETTY_FUNCTION__ << std::endl;
	isl_multi_pw_aff *index;
	int depth;

	index = pet_expr_access_get_index(expr);
	depth = extract_depth(index);
	isl_multi_pw_aff_free(index);

  std::cerr << "done " << __PRETTY_FUNCTION__ << " depth is " << depth << std::endl;
	return depth;
}



// TODO resolve all references as if they were their the rhs of their initialization
Expr* isReference( DeclRefExpr* dref ){
  std::cerr << __PRETTY_FUNCTION__ << std::endl;
  if ( auto decl = dref->getDecl() ) {
    cerr << "got the decl" << endl;
    if ( auto var_decl = dyn_cast_or_null<VarDecl>(decl) ) {
      cerr << "is a var decl" << endl;
      if ( auto type = var_decl->getType().getTypePtr() ) {
	cerr << "got the type" << endl;
	if ( type->isReferenceType() ) {
	  cerr << "is a ref type" << endl;
	  if ( var_decl->hasInit() ) {
	    cerr << "has a init" << endl;
	    return var_decl->getInit();
	  }else{
	    cerr << "a reference has to have a initializer something went wrong here" << endl;
	  }
	}
      }
    }
  }
  return nullptr;
}

// TODO if it is a reference to  cout cerr ... issue a warning
void PetScan::check_stream_reference( DeclRefExpr* expr ){
  auto value_decl = expr->getDecl();
  // check for certain names and type std::ostream

  if ( value_decl->getNameAsString() == "cout" || value_decl->getNameAsString() == "cerr" ) { // TODO more
    auto qual_type = value_decl->getType();
    if ( qual_type.getAsString() == "std::ostream" ) {
      warning_assume_with_extra_string( expr, "stream will get mixed up if parallelized" ); 
    }
  }
}

/* Construct a pet_expr representing an index expression for an access
 * to the variable referenced by "expr".
 *
 * If "expr" references an enum constant, then return an integer expression
 * instead, representing the value of the enum constant.
 */
__isl_give pet_expr *PetScan::extract_index_expr(DeclRefExpr *expr)
{
  std::cerr << __PRETTY_FUNCTION__ << std::endl;
  if ( auto to_expr = isReference( expr )) {
    return extract_index_expr( to_expr );
  }
  check_stream_reference( expr );
  return extract_index_expr(expr->getDecl());
}

/* Construct a pet_expr representing an index expression for an access
 * to the variable "decl".
 *
 * If "decl" is an enum constant, then we return an integer expression
 * instead, representing the value of the enum constant.
 */
__isl_give pet_expr *PetScan::extract_index_expr(ValueDecl *decl)
{
  std::cerr << __PRETTY_FUNCTION__ << std::endl;
	isl_id *id;
	isl_space *space;


	decl->dump();

	if (isa<EnumConstantDecl>(decl))
		return extract_expr(cast<EnumConstantDecl>(decl));

	id = create_decl_id(ctx, decl);
	std::cerr << "id " << id << std::endl;
	space = isl_space_alloc(ctx, 0, 0, 0);
	space = isl_space_set_tuple_id(space, isl_dim_out, id);
	std::cerr << "space " << space << std::endl;

	return pet_expr_from_index(isl_multi_pw_aff_zero(space));
}


bool PetScan::isPureOrConst( FunctionDecl* fdecl ){
  std::cerr << __PRETTY_FUNCTION__ << std::endl;
  for( auto i = fdecl->attr_begin(), e = fdecl->attr_end(); i != e; ++i ){
      if ( isa<ConstAttr>(*i) ) return true;
      if ( isa<PureAttr>(*i) ) return true;
  }  
  std::cerr << "done " << __PRETTY_FUNCTION__ << std::endl;
  return false;
}

void PetScan::checkPureOrConst( CallExpr* call ) {
  std::cerr << __PRETTY_FUNCTION__ << std::endl;

  auto is_decl_pure_or_const = isPureOrConst( call->getDirectCallee() );
  if ( !is_decl_pure_or_const ) {
    std::cerr << __PRETTY_FUNCTION__ << " writing warning" << std::endl;
    //warning_assume( call, "this function always returns the same value while the loop is executed. mark as const or pure if possible" );
    return;
  }else{
    std::cerr << __PRETTY_FUNCTION__ << " writing note" << std::endl;
    note_understood( call, "function call is a call to a const/pure function" );
  }
  
  std::vector<int> args_non_const;
  for (int i = 0; i < call->getNumArgs(); ++i){
    auto arg = call->getArg(i);
    if ( isa<IntegerLiteral>( arg ) ) continue;
    if ( isa<FloatingLiteral>( arg ) ) continue;
    // TODO allow more stuff like constexpr or const 
    args_non_const.push_back( i );
  }

  // issue a warning if the arguments to the function are not const 
  if ( args_non_const.size() !=  0 ) {
    std::string message = "this function is marked const or pure but the arguments ";
    for( auto& arg_id : args_non_const ){
      message += " " + to_string(arg_id);
    }
    message += " may be variable";
    warning_assume( call, message.c_str() ); 
  }
  std::cerr << __PRETTY_FUNCTION__ << std::endl;
}

std::string PetScan::createCallPlaceholder( std::string call_text ) {
	std::string placeholder = "C_" + to_string(call_ctr++);
  // add a placeholder entry to the map
  (*name_to_text)[placeholder] = call_text;
	return placeholder;
}

/* 
 * hack to allow calls to function ins conditions without loosing the affineness constraint
 *
 * simply assume that this function will always return the same value.
 * this way its the same thing like a parameter
 * since i can not put the text of the function call into the variable ( would mess up the isl representation )
 * i will put a placeholder in it which needs to be translated back to the coresponding function call
 *
 */
__isl_give pet_expr *PetScan::extract_index_expr(CallExpr *call)
{
  std::cerr << __PRETTY_FUNCTION__ << std::endl;
  // TODO dont emit the warning if the function is pure or const and has no arguments or if the arguments are
  //      themselfs non changing
  checkPureOrConst( call );

#if 1
  // get the text of how the function was called 
  auto& SM = ast_context.getSourceManager();
  std::string call_text = Lexer::getSourceText( 
      CharSourceRange::getTokenRange( call->getSourceRange() ),
      SM, 
      LangOptions() 
  ) ;

  std::cerr << "call_text " << call_text << std::endl;
#endif

  // create a map between calls and their placeholder
  string placeholder = createCallPlaceholder( call_text );

  // create a decl id from this call
  auto id = isl_id_alloc(ctx,  placeholder.c_str(), cast<NamedDecl>(call->getCalleeDecl()) );
  auto space = isl_space_alloc(ctx, 0, 0, 0);
  space = isl_space_set_tuple_id(space, isl_dim_out, id);

  std::cerr << "done " << __PRETTY_FUNCTION__ << std::endl;
  return pet_expr_from_index(isl_multi_pw_aff_zero(space));
}

/* 
 * hack to allow calls to member functions 
 */
__isl_give pet_expr *PetScan::extract_index_expr(CXXMemberCallExpr *call)
{
  std::cerr << __PRETTY_FUNCTION__ << std::endl;
  // TODO issue a warning if the function is not on of 
  //      std::vector::size()
  //      std::array::size() 
  //      std::string::size()
  //      std::string::length() ...
  
  auto method_decl = call->getMethodDecl();

  std::cerr << "pet member call of declaration fqn: " << method_decl->getQualifiedNameAsString() << std::endl;


  // TODO for the time beeing ok CRITICAL change this and test for the instance to have the type array<T,N>
  auto method_name = method_decl->getNameAsString();
  if ( method_name != "end" || method_name == "begin" ) {
    if ( !method_decl->isConst() ) {
      std::cerr << "pet can not call a non const function" << std::endl;
      return nullptr;
    }
  }

  auto name = method_decl->getQualifiedNameAsString();



#if 1
  // get the text of how the function was called 
  auto& SM = ast_context.getSourceManager();
  std::string call_text = Lexer::getSourceText( 
      CharSourceRange::getTokenRange( call->getSourceRange() ),
      SM, 
      LangOptions() 
  ) ;

  std::cerr << "call_text " << call_text << std::endl;
#endif

  string placeholder = "C_" + to_string(call_ctr++);

  // create a decl id from this call
  auto id = isl_id_alloc(ctx, placeholder.c_str(), cast<NamedDecl>(call->getCalleeDecl()) );
  auto space = isl_space_alloc(ctx, 0, 0, 0);
  space = isl_space_set_tuple_id(space, isl_dim_out, id);

  // add a placeholder entry to the map
  (*name_to_text)[placeholder] = call_text;

  std::cerr << "done " << __PRETTY_FUNCTION__ << std::endl;
  return pet_expr_from_index(isl_multi_pw_aff_zero(space));
}

/* 
 * 
 */
__isl_give pet_expr *PetScan::extract_index_expr(CXXConstructExpr *construct)
{
  std::cerr << __PRETTY_FUNCTION__ << std::endl;
  
  auto n_args = construct->getNumArgs();
  std::cerr << "n args " << n_args << std::endl;
  // TODO 

  if ( n_args != 1 ) {
    unsupported_with_extra_string( construct, " != 1 argument to a construct expr are not implemented" );
    return nullptr;
  }
  
  return extract_index_expr( construct->getArg(0) );
}


/* 
 * 
 */
__isl_give pet_expr *PetScan::extract_index_expr(MaterializeTemporaryExpr *temp)
{
  std::cerr << __PRETTY_FUNCTION__ << std::endl;
  auto expr = temp->GetTemporaryExpr();

  return extract_index_expr( expr );
}

/* 
 * extract from string literal
 */
__isl_give pet_expr *PetScan::extract_index_expr(StringLiteral *slit)
{
  std::cerr << __PRETTY_FUNCTION__ << std::endl;

  //std::string id_name = slit->getString();
  static int ctr = 0;
  string id_name = "constant_string_" + to_string(ctr++);

  auto id = isl_id_alloc(ctx, id_name.c_str(), register_user_data_type( slit, ITI_StringLiteral ) );
  auto space = isl_space_alloc(ctx, 0, 0, 0);
  space = isl_space_set_tuple_id(space, isl_dim_out, id);

  std::cerr << "done " << __PRETTY_FUNCTION__ << std::endl;
  return pet_expr_from_index(isl_multi_pw_aff_zero(space));
}

/* Construct a pet_expr representing the index expression "expr"
 * Return NULL on error.
 *
 * If "expr" is a reference to an enum constant, then return
 * an integer expression instead, representing the value of the enum constant.
 */
__isl_give pet_expr *PetScan::extract_index_expr(Expr *expr)
{
  std::cerr << __PRETTY_FUNCTION__ << expr << std::endl;
	switch (expr->getStmtClass()) {
	case Stmt::ImplicitCastExprClass:
		return extract_index_expr(cast<ImplicitCastExpr>(expr));
	case Stmt::DeclRefExprClass:
		return extract_index_expr(cast<DeclRefExpr>(expr));
	case Stmt::ArraySubscriptExprClass:
		return extract_index_expr(cast<ArraySubscriptExpr>(expr));
	case Stmt::IntegerLiteralClass:
		return extract_expr(cast<IntegerLiteral>(expr));
	case Stmt::MemberExprClass:
		return extract_index_expr(cast<MemberExpr>(expr));
	case Stmt::CXXOperatorCallExprClass:
		return extract_index_expr(cast<CXXOperatorCallExpr>(expr));
	case Stmt::CallExprClass:
		return extract_index_expr(cast<CallExpr>(expr));
	case Stmt::CXXMemberCallExprClass:
		return extract_index_expr(cast<CXXMemberCallExpr>(expr));
	case Stmt::CXXConstructExprClass:
		return extract_index_expr(cast<CXXConstructExpr>(expr));
	case Stmt::MaterializeTemporaryExprClass:
		return extract_index_expr(cast<MaterializeTemporaryExpr>(expr));
	case Stmt::StringLiteralClass:
		return extract_index_expr(cast<StringLiteral>(expr));
	default:
		unsupported(expr);
	}
	return NULL;
}


__isl_give pet_expr* PetScan::build_access_by_subscript_from_iterator ( Expr* iterator ) {
  cerr << __PRETTY_FUNCTION__ << endl;
  auto base_expr = build_base_expression_by_initializer( ignoreImplicitCast(iterator) );
  base_expr->dump();
  cerr << "extracting from base_expr " << endl;
  if ( auto pet_base_expr = extract_index_expr( base_expr ) ) {
      DeclRefExpr* index = build_index_expression_by_decl( ignoreImplicitCast(iterator) );
      index->dump();
      cerr << "extracting from index_expr " << endl;
      if ( auto pet_index_expr = extract_index_expr( index ) ) {
              cerr << "got base and index extracted " << endl;
              auto access_by_subscript = pet_expr_access_subscript(pet_base_expr, pet_index_expr);
              pet_expr_dump( access_by_subscript );
              return access_by_subscript;
      }
  }
  cerr << "reaching end of " << __PRETTY_FUNCTION__ << " most likly an error" << endl;
  return nullptr;
}
// helper function for extract_index_expr CXXOperatorCallExpr for unary operators 
__isl_give pet_expr *PetScan::extract_index_expr_unary(CXXOperatorCallExpr *expr){

	auto arg0 = expr->getArg(0);
	auto ook = expr->getOperator();

	// if ook is OO_Star and the accessed element is a iterator 
	// generate an array access 
	if ( ook == OO_Star ) {
          cerr << "ook is a OO_Star " << endl;
          auto expr = ignoreImplicitCast( arg0 );

	  if ( isIteratorType( expr->getType() ) ) {
            cerr << "OO_Star operation dereferences an iterator" << std::endl;
            return build_access_by_subscript_from_iterator( expr );
          }
	}

	return nullptr;
}

// TODO CXXOperatorCall does not just cover the operator [] but also the assign operator between statements
__isl_give pet_expr *PetScan::extract_index_expr(clang::CXXOperatorCallExpr *expr){

	std::cerr << __PRETTY_FUNCTION__ << std::endl;

	if ( expr->getNumArgs() == 1 ) {
		return extract_index_expr_unary( expr );
	}
	// check the argument count 
	if ( expr->getNumArgs() != 2 ) {
	  unsupported_msg( expr, "number of arguments is != 2" );
	  return nullptr;
	}
	
	// TODO dont allow to call this on objects that are other then vector or array ( atleast until this is fully implemented )
	auto function_decl = expr->getDirectCallee();
	std::cerr << "pet name of the operator called is " << function_decl->getQualifiedNameAsString() << std::endl;
	auto method_decl = dyn_cast_or_null<CXXMethodDecl>(function_decl);
	if ( !method_decl ) {
	  unsupported_with_extra_string( expr, "cxx operator call needs to call a method not a function" );
	  return nullptr;
	}

	auto cxx_record_decl = method_decl->getParent(); 
	auto type = cxx_record_decl->getTypeForDecl();

	if ( !isRandomAccessStlType( type ) ) {
	  unsupported_with_extra_string( expr, "the object you are calling this method from is not a random access container" );
	  return nullptr;
	}	

	// check the operator type to be a subscript operation
	if ( expr->getOperator() != OO_Subscript ){
	  std::cerr << "dumping expr " << std::endl;
	  expr->dump();
	  unsupported_msg( expr, "the overloaded function called is not a subscript operator" );
	  return nullptr;
	}

	Expr *base = expr->getArg(0); // should be the base 
	Expr *idx = expr->getArg(1); // should be the index

	base->dump();
	idx->dump();

	pet_expr *base_expr = extract_index_expr(base);
	pet_expr *index = extract_expr(idx);

	base_expr = pet_expr_access_subscript(base_expr, index);
	cerr << "dumping generated accesss expression" << endl;
	pet_expr_dump( base_expr );

	cerr << "done " << __PRETTY_FUNCTION__ << endl;
	return base_expr;
}

/* Extract an index expression from the given array subscript expression.
 *
 * We first extract an index expression from the base.
 * This will result in an index expression with a range that corresponds
 * to the earlier indices.
 * We then extract the current index and let
 * pet_expr_access_subscript combine the two.
 */
__isl_give pet_expr *PetScan::extract_index_expr(ArraySubscriptExpr *expr)
{
	Expr *base = expr->getBase();
	Expr *idx = expr->getIdx();
	pet_expr *index;
	pet_expr *base_expr;

	base_expr = extract_index_expr(base);
	index = extract_expr(idx);

	base_expr = pet_expr_access_subscript(base_expr, index);

	return base_expr;
}

/* Extract an index expression from a member expression.
 *
 * If the base access (to the structure containing the member)
 * is of the form
 *
 *	A[..]
 *
 * and the member is called "f", then the member access is of
 * the form
 *
 *	A_f[A[..] -> f[]]
 *
 * If the member access is to an anonymous struct, then simply return
 *
 *	A[..]
 *
 * If the member access in the source code is of the form
 *
 *	A->f
 *
 * then it is treated as
 *
 *	A[0].f
 */
__isl_give pet_expr *PetScan::extract_index_expr(MemberExpr *expr)
{
	Expr *base = expr->getBase();
	FieldDecl *field = cast<FieldDecl>(expr->getMemberDecl());
	pet_expr *base_index;
	isl_id *id;

	base_index = extract_index_expr(base);

	if (expr->isArrow()) {
		pet_expr *index = pet_expr_new_int(isl_val_zero(ctx));
		base_index = pet_expr_access_subscript(base_index, index);
	}

	if (field->isAnonymousStructOrUnion())
		return base_index;

	id = create_decl_id(ctx, field);

	return pet_expr_access_member(base_index, id);
}

/* Mark the given access pet_expr as a write.
 */
static __isl_give pet_expr *mark_write(__isl_take pet_expr *access)
{
	access = pet_expr_access_set_write(access, 1);
	access = pet_expr_access_set_read(access, 0);

	return access;
}

/* Mark the given (read) access pet_expr as also possibly being written.
 * That is, initialize the may write access relation from the may read relation
 * and initialize the must write access relation to the empty relation.
 */
static __isl_give pet_expr *mark_may_write(__isl_take pet_expr *expr)
{
	isl_union_map *access;
	isl_union_map *empty;

	access = pet_expr_access_get_dependent_access(expr,
						pet_expr_access_may_read);
	empty = isl_union_map_empty(isl_union_map_get_space(access));
	expr = pet_expr_access_set_access(expr, pet_expr_access_may_write,
					    access);
	expr = pet_expr_access_set_access(expr, pet_expr_access_must_write,
					    empty);

	return expr;
}

/* Construct a pet_expr representing a unary operator expression.
 */
__isl_give pet_expr *PetScan::extract_expr(UnaryOperator *expr)
{
	cerr << __PRETTY_FUNCTION__ << endl;
	int type_size;
	pet_expr *arg;
	enum pet_op_type op;

	op = UnaryOperatorKind2pet_op_type(expr->getOpcode());
	if (op == pet_op_last) {
		unsupported(expr);
		return NULL;
	}

        // handle dereference operations
        if ( op == pet_op_deref ) {
          // handle dereference of array<T,N>::iterator 
          auto sub_expr = expr->getSubExpr();
          if ( isIterator( sub_expr ) ) {
            cerr << "pet_op_deref dereferences an iterator " << endl;
            return build_access_by_subscript_from_iterator( ignoreImplicitCast(sub_expr) );
          }
        }

        arg = extract_expr(expr->getSubExpr());

	if (expr->isIncrementDecrementOp() &&
	    pet_expr_get_type(arg) == pet_expr_access) {
		arg = mark_write(arg);
		arg = pet_expr_access_set_read(arg, 1);
	}



	type_size = get_type_size(expr->getType(), ast_context);
	//return pet_expr_access_set_user(pet_expr_new_unary(type_size, op, arg), expr);
	return pet_expr_new_unary(type_size, op, arg);
}

/* Construct a pet_expr representing a binary operator expression.
 *
 * If the top level operator is an assignment and the LHS is an access,
 * then we mark that access as a write.  If the operator is a compound
 * assignment, the access is marked as both a read and a write.
 */
__isl_give pet_expr *PetScan::extract_expr(BinaryOperator *expr)
{
  cerr << __PRETTY_FUNCTION__ << endl;
	int type_size;
	pet_expr *lhs, *rhs;
	enum pet_op_type op;

	op = BinaryOperatorKind2pet_op_type(expr->getOpcode());
	if (op == pet_op_last) {
		unsupported(expr);
		return NULL;
	}

        // check wether we compare between iterator and <container>.end()
        if ( op == pet_op_ne ) {
          if ( auto binary_operator = build_iterator_unequal_comparison( expr->getLHS(), expr->getRHS() ) ) {
            return binary_operator;
          }
        }

	lhs = extract_expr(expr->getLHS());
	rhs = extract_expr(expr->getRHS());

	if (expr->isAssignmentOp() &&
	    pet_expr_get_type(lhs) == pet_expr_access) {
		lhs = mark_write(lhs);
		if (expr->isCompoundAssignmentOp()) {
		    lhs = pet_expr_access_set_read(lhs, 1);
		    // check that the LHS is not an array
		    auto clang_lhs = expr->getLHS();
		    auto qtype = clang_lhs->getType();
		    auto type = qtype.getTypePtr();
		    if ( !type->isArrayType() ) {
		      lhs = pet_expr_access_set_reduction( lhs , 1, op );
		    }
		}
	}

	std::cerr << "get_type_size in BinaryOperator " << std::endl;
	type_size = get_type_size(expr->getType(), ast_context);
	std::cerr << "done get_type_size in BinaryOperator test" << std::endl;
	cerr << "binaryOperator " << type_size << " " << op << endl;
	return pet_expr_new_binary(type_size, op, lhs, rhs);
}

/* Construct a pet_tree for a variable declaration.
 */
__isl_give pet_tree *PetScan::extract(Decl *decl)
{
    std::cerr << __PRETTY_FUNCTION__ << std::endl;

    if ( auto vd = dyn_cast_or_null<VarDecl>(decl) ) {

      std::cerr << "is a vardecl" << std::endl;

      pet_expr *lhs, *rhs;
      pet_tree *tree;

      lhs = extract_access_expr(vd);
      lhs = mark_write(lhs);
      if (!vd->getInit()){
	      tree = pet_tree_new_decl(lhs);
	      std::cerr << "no init new pet tree for decl " << tree << std::endl;
      }else {
	      std::cerr << "staring to extract expr" << std::endl;
	      rhs = extract_expr(vd->getInit());
	      std::cerr << "done extracting expr" << std::endl;
	      tree = pet_tree_new_decl_init(lhs, rhs);
	      std::cerr << "init new pet tree for decl " << tree << std::endl;
      }
      return tree;
    }

    if ( auto typedf_decl = dyn_cast_or_null<TypedefDecl>( decl ) ) {
      std::cerr << "pet this is a typedef decl and can be ignored" << std::endl;
      // TODO CRITICAL i dont belive that its ok to return nullptr since the expression needs to be marked as 
      //               "ignored" or something like this
      return nullptr;
    }

    return nullptr;
}

/* Construct a pet_tree for a variable declaration statement.
 * If the declaration statement declares multiple variables,
 * then return a group of pet_trees, one for each declared variable.
 */
__isl_give pet_tree *PetScan::extract(DeclStmt *stmt)
{
	std::cerr << __PRETTY_FUNCTION__ << std::endl;


	pet_tree *tree;
	unsigned n;

	if (!stmt->isSingleDecl()) {
		const DeclGroup &group = stmt->getDeclGroup().getDeclGroup();
		n = group.size();
		tree = pet_tree_new_block(ctx, 0, n);

		for (int i = 0; i < n; ++i) {
			pet_tree *tree_i;
			pet_loc *loc;


			std::cerr << __PRETTY_FUNCTION__ << "extract group[i]" << std::endl;
			tree_i = extract(group[i]);
			loc = construct_pet_loc(group[i]->getSourceRange(),
						false);
			tree_i = pet_tree_set_loc(tree_i, loc);
			tree = pet_tree_block_add_child(tree, tree_i);
		}

		return tree;
	}

	auto* ret = extract(stmt->getSingleDecl());
	std::cerr << "done " << __PRETTY_FUNCTION__ << " ret is " << ret << std::endl;
	return ret;
}

/* Construct a pet_expr representing a conditional operation.
 */
__isl_give pet_expr *PetScan::extract_expr(ConditionalOperator *expr)
{
	pet_expr *cond, *lhs, *rhs;
	isl_pw_aff *pa;

	cond = extract_expr(expr->getCond());
	lhs = extract_expr(expr->getTrueExpr());
	rhs = extract_expr(expr->getFalseExpr());

	return pet_expr_new_ternary(cond, lhs, rhs);
}

__isl_give pet_expr *PetScan::extract_expr(ImplicitCastExpr *expr)
{
	return extract_expr(expr->getSubExpr());
}

/* Construct a pet_expr representing a floating point value.
 *
 * If the floating point literal does not appear in a macro,
 * then we use the original representation in the source code
 * as the string representation.  Otherwise, we use the pretty
 * printer to produce a string representation.
 */
__isl_give pet_expr *PetScan::extract_expr(FloatingLiteral *expr)
{
	double d;
	string s;
	const LangOptions &LO = ast_context.getLangOpts();
	SourceLocation loc = expr->getLocation();

	if (!loc.isMacroID()) {
		SourceManager &SM = ast_context.getSourceManager();
		unsigned len = Lexer::MeasureTokenLength(loc, SM, LO);
		s = string(SM.getCharacterData(loc), len);
	} else {
		llvm::raw_string_ostream S(s);
		expr->printPretty(S, 0, PrintingPolicy(LO));
		S.str();
	}
	d = expr->getValueAsApproximateDouble();
	return pet_expr_new_double(ctx, d, s.c_str());
}

/* Convert the index expression "index" into an access pet_expr of type "qt".
 */
__isl_give pet_expr *PetScan::extract_access_expr(QualType qt,
	__isl_take pet_expr *index)
{
	std::cerr << __PRETTY_FUNCTION__ << std::endl;

	int depth;
	int type_size;

	depth = extract_depth(index);
	type_size = get_type_size(qt, ast_context);

	index = pet_expr_set_type_size(index, type_size);
	index = pet_expr_access_set_depth(index, depth);

	std::cerr << "depth " << depth << " type size " << type_size << std::endl;
	std::cerr << "done " << __PRETTY_FUNCTION__ << std::endl;
	return index;
}


/* Extract an index expression from "expr" and then convert it into
 * an access pet_expr.
 *
 * If "expr" is a reference to an enum constant, then return
 * an integer expression instead, representing the value of the enum constant.
 */
__isl_give pet_expr *PetScan::extract_access_expr(Expr *expr)
{
	std::cerr << __PRETTY_FUNCTION__ << std::endl;
	pet_expr *index;

	index = extract_index_expr(expr);
	std::cerr << "extracting information from expr dumping:" << std::endl;
	expr->dump();
	std::cerr << "done dumping :" << std::endl;

	if (pet_expr_get_type(index) == pet_expr_int){
		cerr << "pet expr type is int -> returing index" << endl;
		return index;
	}

	cerr << "pet expr type is not int -> extracting access form this expr" << endl;
	auto ret = extract_access_expr(expr->getType(), index);
	
	return ret;
}

/* Extract an index expression from "decl" and then convert it into
 * an access pet_expr.
 */
__isl_give pet_expr *PetScan::extract_access_expr(ValueDecl *decl)
{
	std::cerr << __PRETTY_FUNCTION__ << std::endl;
	return extract_access_expr(decl->getType(), extract_index_expr(decl));
}

__isl_give pet_expr *PetScan::extract_expr(ParenExpr *expr)
{
	return extract_expr(expr->getSubExpr());
}

/* Extract an assume statement from the argument "expr"
 * of a __pencil_assume statement.
 */
__isl_give pet_expr *PetScan::extract_assume(Expr *expr)
{
	return pet_expr_new_unary(0, pet_op_assume, extract_expr(expr));
}

/* Construct a pet_expr corresponding to the function call argument "expr".
 * The argument appears in position "pos" of a call to function "fd".
 *
 * If we are passing along a pointer to an array element
 * or an entire row or even higher dimensional slice of an array,
 * then the function being called may write into the array.
 *
 * We assume here that if the function is declared to take a pointer
 * to a const type, then the function may only perform a read
 * and that otherwise, it may either perform a read or a write (or both).
 * We only perform this check if "detect_writes" is set.
 */
__isl_give pet_expr *PetScan::extract_argument(FunctionDecl *fd, int pos,
	Expr *expr, bool detect_writes)
{
	std::cerr << __PRETTY_FUNCTION__ << " " << __LINE__ << std::endl;
	pet_expr *res;
	int is_addr = 0, is_partial = 0;

	while (expr->getStmtClass() == Stmt::ImplicitCastExprClass) {
		ImplicitCastExpr *ice = cast<ImplicitCastExpr>(expr);
		expr = ice->getSubExpr();
	}
	if (expr->getStmtClass() == Stmt::UnaryOperatorClass) {
		UnaryOperator *op = cast<UnaryOperator>(expr);
		if (op->getOpcode() == UO_AddrOf) {
			is_addr = 1;
			expr = op->getSubExpr();
		}
	}

	// special handling for CXXDefaultArgExpr case
	if ( auto default_arg = dyn_cast_or_null<CXXDefaultArgExpr>(expr) ) {
	  // we can get the default args substitution from the declaration
	  auto expr = default_arg->getExpr();

	  // analyze this expr
	  auto res = extract_expr( expr );

	  // it can not be a writing expr 
	  // since the function decl can not know anything about the caller and 
	  // due to this nothing about the variables or arrays of the caller
	  return res;
	}

	res = extract_expr(expr);

	if (!res)
		return NULL;
	if (array_depth(expr->getType().getTypePtr()) > 0)
		is_partial = 1;
	if (detect_writes && (is_addr || is_partial) && pet_expr_get_type(res) == pet_expr_access) {
		ParmVarDecl *parm;
		if (!fd->hasPrototype()) {
			report_prototype_required(expr);
			return pet_expr_free(res);
		}

		if ( fd->isVariadic() && pos >= fd->getNumParams() ) {
		  unsupported_with_extra_string( expr, "this argument is passed to a variadic functions variadic part -> cannot determin constness -> assuming const !" );
		}else{
		  parm = fd->getParamDecl(pos);
		  if (!const_base(parm->getType())){
		    res = mark_may_write(res);
		  }
		}
	}

	if (is_addr)
		res = pet_expr_new_unary(0, pet_op_address_of, res);
	std::cerr << __PRETTY_FUNCTION__ << " done " << __LINE__ << std::endl;
	return res;
}

/* Find the first FunctionDecl with the given name.
 * "call" is the corresponding call expression and is only used
 * for reporting errors.
 *
 * Return NULL on error.
 */
FunctionDecl *PetScan::find_decl_from_name(CallExpr *call, string name)
{
	TranslationUnitDecl *tu = ast_context.getTranslationUnitDecl();
	DeclContext::decl_iterator begin = tu->decls_begin();
	DeclContext::decl_iterator end = tu->decls_end();
	for (DeclContext::decl_iterator i = begin; i != end; ++i) {
		FunctionDecl *fd = dyn_cast<FunctionDecl>(*i);
		if (!fd)
			continue;
		if (fd->getName().str().compare(name) != 0)
			continue;
		if (fd->hasBody())
			return fd;
		report_missing_summary_function_body(call);
		return NULL;
	}
	report_missing_summary_function(call);
	return NULL;
}

/* Return the FunctionDecl for the summary function associated to the
 * function called by "call".
 *
 * In particular, if the pencil option is set, then
 * search for an annotate attribute formatted as
 * "pencil_access(name)", where "name" is the name of the summary function.
 *
 * If no summary function was specified, then return the FunctionDecl
 * that is actually being called.
 *
 * Return NULL on error.
 */
FunctionDecl *PetScan::get_summary_function(CallExpr *call)
{
	std::cerr << __PRETTY_FUNCTION__ << " " << __LINE__ << std::endl;
	FunctionDecl *decl = call->getDirectCallee();
	if (!decl)
		return NULL;

	if (!options->pencil)
		return decl;

	specific_attr_iterator<AnnotateAttr> begin, end, i;
	begin = decl->specific_attr_begin<AnnotateAttr>();
	end = decl->specific_attr_end<AnnotateAttr>();
	for (i = begin; i != end; ++i) {
		string attr = (*i)->getAnnotation().str();

		const char prefix[] = "pencil_access(";
		size_t start = attr.find(prefix);
		if (start == string::npos)
			continue;
		start += strlen(prefix);
		string name = attr.substr(start, attr.find(')') - start);

		return find_decl_from_name(call, name);
	}
	std::cerr << __PRETTY_FUNCTION__ << " done " << __LINE__ << std::endl;

	return decl;
}

/* Construct a pet_expr representing a function call.
 *
 * In the special case of a "call" to __pencil_assume,
 * construct an assume expression instead.
 *
 * In the case of a "call" to __pencil_kill, the arguments
 * are neither read nor written (only killed), so there
 * is no need to check for writes to these arguments.
 *
 * __pencil_assume and __pencil_kill are only recognized
 * when the pencil option is set.
 */
__isl_give pet_expr *PetScan::extract_expr(CallExpr *expr)
{
	std::cerr << __PRETTY_FUNCTION__ << std::endl;
	pet_expr *res = NULL;
	FunctionDecl *fd;
	string name;
	unsigned n_arg;
	bool is_kill;

	fd = expr->getDirectCallee();
	if (!fd) {

	  // patch for generic lambda 
	  // if no direct callee declaration could be found 
	  // this can mean that we are calling something from a generic lambda
	  // the only thing we have is a name 
	  
	  auto callee = expr->getCallee();
	  callee->dumpColor();
	  if ( auto dep_scope_member_expr = dyn_cast_or_null<CXXDependentScopeMemberExpr>( callee ) ) {
	    auto member = dep_scope_member_expr->getMember();
	    std::cerr << member.getAsString() << std::endl;
	    name = member.getAsString();
	    if ( auto base = dep_scope_member_expr->getBase() ) {
	      base->dumpColor();
	      if ( auto decl_ref = dyn_cast_or_null<DeclRefExpr>( base ) ) {
		if ( auto decl = decl_ref->getDecl() ) {
		  decl->dumpColor();
		  if ( auto type = decl->getType().getTypePtr() ) {
		    type->dump();
		  }
		}
	      }
	    }
	  }else{
	    std::cerr << " is not a CXXDependentScopeMemberExpr " << std::endl;
	  }


	  // end patch

	  unsupported(expr);
	  expr->dumpColor();
	  return NULL;
	}

	name = fd->getDeclName().getAsString();
	n_arg = expr->getNumArgs();


#if 1
	// TODO get the arguments of the function 
	// and correct them to their c coresponding function
	// otherwise is_affine_builtin will not detect them 
	if ( name == "floor" ){
	  name = "floord";
	}

	// TODO if the name is not known to be a buildin continue with extract_access_expr
	//      if treat_calls_like_access is set
	if ( ! ( 
	      is_affine_builtin( 0, n_arg, name.c_str() ) || 
	      is_affine_builtin( 1, n_arg, name.c_str() ) 
	      ) 
	   ){
	  if ( treat_calls_like_access ) {
	    std::cerr << "is not a affine built-in -> extracting access" << std::endl;
	    return extract_access_expr( expr );
	  }
	}
#endif

	if (options->pencil && n_arg == 1 && name == "__pencil_assume")
		return extract_assume(expr->getArg(0));
	is_kill = options->pencil && name == "__pencil_kill";

	res = pet_expr_new_call(ctx, name.c_str(), n_arg);
	if (!res)
		return NULL;

	for (int i = 0; i < n_arg; ++i) {
		Expr *arg = expr->getArg(i);
		res = pet_expr_set_arg(res, i,
			    PetScan::extract_argument(fd, i, arg, !is_kill));
	}

	fd = get_summary_function(expr);
	if (!fd)
		return pet_expr_free(res);

	res = set_summary(res, fd);

	std::cerr << "done " << __PRETTY_FUNCTION__ << std::endl;
	return res;
}

/* Construct a pet_expr representing a member call expr
 */
__isl_give pet_expr *PetScan::extract_expr(CXXMemberCallExpr *expr)
{
	std::cerr << __PRETTY_FUNCTION__ << std::endl;
	pet_expr *res = NULL;
	FunctionDecl *fd;
	string name;
	unsigned n_arg;
	bool is_kill;

	fd = expr->getDirectCallee();
	if (!fd) {
		unsupported(expr);
		return NULL;
	}

	// dont allow calls to non const functions
	auto method_decl = expr->getMethodDecl();
	if ( !method_decl->isConst() ) {
	  unsupported_with_extra_string( expr, "the function called is not const and will change the state of the object" );
	  return nullptr;
	}
	

	name = fd->getDeclName().getAsString();
	std::cerr << __PRETTY_FUNCTION__ << " " << __LINE__ << " " << " name is TODO may need fqn " << name << std::endl;
	n_arg = expr->getNumArgs();

	if (options->pencil && n_arg == 1 && name == "__pencil_assume")
		return extract_assume(expr->getArg(0));
	is_kill = options->pencil && name == "__pencil_kill";

	std::cerr << __PRETTY_FUNCTION__ << " " << __LINE__ << std::endl;
	res = pet_expr_new_call(ctx, name.c_str(), n_arg);
	if (!res)
		return NULL;

	for (int i = 0; i < n_arg; ++i) {
	  Expr *arg = expr->getArg(i);
	  res = pet_expr_set_arg(res, i,
		      PetScan::extract_argument(fd, i, arg, !is_kill));
	}

	fd = get_summary_function(expr);
	if (!fd)
		return pet_expr_free(res);

	res = set_summary(res, fd);

	std::cerr << "done " << __PRETTY_FUNCTION__ << std::endl;
	return res;
}

/* Construct a pet_expr representing a (C style) cast.
 */
__isl_give pet_expr *PetScan::extract_expr(CStyleCastExpr *expr)
{
	pet_expr *arg;
	QualType type;

	arg = extract_expr(expr->getSubExpr());
	if (!arg)
		return NULL;

	type = expr->getTypeAsWritten();
	return pet_expr_new_cast(type.getAsString().c_str(), arg);
}

/* Construct a pet_expr representing an integer.
 */
__isl_give pet_expr *PetScan::extract_expr(IntegerLiteral *expr)
{
	return pet_expr_new_int(extract_int(expr));
}

/* Construct a pet_expr representing an integer.
 */
__isl_give pet_expr *PetScan::extract_expr(CXXBoolLiteralExpr *expr)
{
  if ( expr->getValue() ) {
    return pet_expr_new_int(isl_val_one(ctx));
  }else{
    return pet_expr_new_int(isl_val_zero(ctx));
  }
  return nullptr;
}

/* Construct a pet_expr representing the integer enum constant "ecd".
 */
__isl_give pet_expr *PetScan::extract_expr(EnumConstantDecl *ecd)
{
	isl_val *v;
	const llvm::APSInt &init = ecd->getInitVal();
	v = ::extract_int(ctx, init.isSigned(), init);
	return pet_expr_new_int(v);
}

// TODO add all assignment operators to this 
bool isAssignmentOp( OverloadedOperatorKind ook ) {
  switch( ook ) {
    case OO_Equal:
      return true;
  }
  return false;
}

//  ‘OO_New’ not handled in switch [-Wswitch]
//  ‘OO_Delete’ not handled in switch [-Wswitch]
//  ‘OO_Array_New’ not handled in switch [-Wswitch]
//  ‘OO_Array_Delete’ not handled in switch [-Wswitch]
//  ‘OO_Plus’ not handled in switch [-Wswitch]
//  ‘OO_Minus’ not handled in switch [-Wswitch]
//  ‘OO_Star’ not handled in switch [-Wswitch]
//  ‘OO_Slash’ not handled in switch [-Wswitch]
//  ‘OO_Percent’ not handled in switch [-Wswitch]
//  ‘OO_Caret’ not handled in switch [-Wswitch]
//  ‘OO_Amp’ not handled in switch [-Wswitch]
//  ‘OO_Pipe’ not handled in switch [-Wswitch]
//  ‘OO_Tilde’ not handled in switch [-Wswitch]
//  ‘OO_Exclaim’ not handled in switch [-Wswitch]
//  ‘OO_Less’ not handled in switch [-Wswitch]
//  ‘OO_Greater’ not handled in switch [-Wswitch]
//  ‘OO_PlusEqual’ not handled in switch [-Wswitch]
//  ‘OO_MinusEqual’ not handled in switch [-Wswitch]
//  ‘OO_StarEqual’ not handled in switch [-Wswitch]
//  ‘OO_SlashEqual’ not handled in switch [-Wswitch]
//  ‘OO_PercentEqual’ not handled in switch [-Wswitch]
//  ‘OO_CaretEqual’ not handled in switch [-Wswitch]
//  ‘OO_AmpEqual’ not handled in switch [-Wswitch]
//  ‘OO_PipeEqual’ not handled in switch [-Wswitch]
//  ‘OO_LessLess’ not handled in switch [-Wswitch]
//  ‘OO_GreaterGreater’ not handled in switch [-Wswitch]
//  ‘OO_LessLessEqual’ not handled in switch [-Wswitch]
//  ‘OO_GreaterGreaterEqual’ not handled in switch [-Wswitch]
//  ‘OO_EqualEqual’ not handled in switch [-Wswitch]
//  ‘OO_ExclaimEqual’ not handled in switch [-Wswitch]
//  ‘OO_LessEqual’ not handled in switch [-Wswitch]
//  ‘OO_GreaterEqual’ not handled in switch [-Wswitch]
//  ‘OO_AmpAmp’ not handled in switch [-Wswitch]
//  ‘OO_PipePipe’ not handled in switch [-Wswitch]
//  ‘OO_PlusPlus’ not handled in switch [-Wswitch]
//  ‘OO_MinusMinus’ not handled in switch [-Wswitch]
//  ‘OO_Comma’ not handled in switch [-Wswitch]
//  ‘OO_ArrowStar’ not handled in switch [-Wswitch]
//  ‘OO_Arrow’ not handled in switch [-Wswitch]
//  ‘OO_Call’ not handled in switch [-Wswitch]
//  ‘OO_Conditional’ not handled in switch [-Wswitch]
//  ‘OO_Coawait’ not handled in switch [-Wswitch]
//  ‘NUM_OVERLOADED_OPERATORS’ not handled in switch [-Wswitch]

// TODO add all assignment operators to this 
bool isCompoundAssignmentOp( OverloadedOperatorKind ook ) {
  switch( ook ) {
    case OO_GreaterEqual:
    case OO_LessEqual:
    case OO_ExclaimEqual:
    case OO_GreaterGreaterEqual:
    case OO_LessLessEqual:
    case OO_PipeEqual:
    case OO_AmpEqual:
    case OO_CaretEqual:
    case OO_PercentEqual:
    case OO_SlashEqual:
    case OO_StarEqual:
    case OO_MinusEqual:
    case OO_PlusEqual:
      return true;
  }
  return false;
}

// if e is a member call expression
// if e is a template function call expression
// TODO test this with std::begin( constant array )
VarDecl *PetScan::extract_member_call(Expr *e) {
  if (auto member_call = dyn_cast_or_null<CXXMemberCallExpr>(e)) {
    cerr << "container begin is referenced by a CXXMemberCallExpr" << endl;
    if (auto instance = member_call->getImplicitObjectArgument()) {
      cerr << " implicit object argument " << instance << endl;
      if (auto decl_ref_expr = dyn_cast_or_null<DeclRefExpr>(instance)) {
        auto type = decl_ref_expr->getType().getTypePtr();

        auto fd = member_call->getDirectCallee();
        auto name = fd->getDeclName().getAsString();
        cerr << "function called is " << name << endl;

        // TODO if the function is one of the iterator functions and the
        // instance called is a random access container return the containers
        // decl
        if (isRandomAccessStlType(type) &&
            isStdContainerIteratorCreator(name)) {
          cerr << "is container and call to begin end rbegin ... " << endl;
          if (auto var_decl = dyn_cast_or_null<VarDecl>(decl_ref_expr->getDecl())) {
            return var_decl;
          }
        }
      } else {
        cerr << "implicit object argument is not followed by a decl_ref_expr but:" << endl;
        instance->dump();
      }
    }
  } else {
    e->dump();
  }

  return nullptr;
  // to catch containers referenced via std::begin( container )
}

VarDecl* PetScan::get_or_create_iterator_replacement( VarDecl* iterator_decl ) {
	auto item = iterator_to_index_map.find( iterator_decl ); 
	if ( item != iterator_to_index_map.end() ) return item->second ;

	cerr << "create a var decl with the same name but a different type" << endl;
	auto vd = create_VarDecl( iterator_decl, &ast_context ); 
	vd->dump();
	iterator_to_index_map[iterator_decl] = vd;
}

static CXXMethodDecl* find_size_method( Decl* decl  ) {

	cerr << __PRETTY_FUNCTION__ << endl;
	if ( auto specialization_decl = dyn_cast_or_null<ClassTemplateSpecializationDecl>( decl ) ) {
		cerr << __PRETTY_FUNCTION__ << endl;
		for ( auto cxx_method : specialization_decl->methods() ){
			auto name = cxx_method->getDeclName().getAsString();
			cerr << "method " << name << endl;
			if ( name == "size" ) {
				cerr << "found size method" << endl;
				return cxx_method;
			}
		}
	}
	return nullptr;
}

std::string 
PetScan::get_container_name_from_iterator( Expr* expr ) {
  if ( auto impl_cast = ignoreImplicitCast( expr ) ){ 
    if ( auto decl_ref_expr = dyn_cast_or_null<DeclRefExpr>(impl_cast) ){
      if ( auto decl = decl_ref_expr->getDecl() ) {
        if ( auto var_decl = dyn_cast_or_null<VarDecl>( decl ) ) {
          if ( var_decl->hasInit() ) {
            auto init = var_decl->getInit();
            if ( auto container_decl = extract_container( init ) ) {
              return container_decl->getNameAsString();
            }
          }
        }
      }
    }
  }
  return "";
}


// check lhs for beeing an iterator
VarDecl*
PetScan::isIterator(Expr* expr){
  if ( auto impl_cast = ignoreImplicitCast( expr ) ){ 
          if ( auto decl_ref_expr = dyn_cast_or_null<DeclRefExpr>(impl_cast) ){
                  if ( auto decl = decl_ref_expr->getDecl() ) {
                          auto type = decl->getType();
                          if ( isIteratorType( type ) ) {
                            return (VarDecl*)decl;
                          }
                  }
          }else{
                  cerr << " not a declref " << endl;
                  expr->dump();
          }
  }
  return nullptr;
};


__isl_give pet_expr* 
PetScan::build_iterator_less_then_comparison_from_expr( Expr* expr, Expr* lhs ) {
  if ( auto cxx_member_call_expr = dyn_cast_or_null<CXXMemberCallExpr>( expr ) ) {
        cerr << __LINE__ << endl;
        if ( auto instance = cxx_member_call_expr->getImplicitObjectArgument() ) {
                cerr << __LINE__ << endl;

                // for the case the container was referenced by its instance and .begin() .end() ...
                if ( auto decl_ref_expr = dyn_cast_or_null<DeclRefExpr>( instance ) ) {
                        cerr << __LINE__ << endl;
                        auto md = cxx_member_call_expr->getDirectCallee();
                        auto name = md->getDeclName().getAsString();
                        if ( name == "end" || name == "cend" ) {
                                cerr << "name of the function called on this object is 'end' " << endl;
                                
                                // TODO CRITICAL you have to check for the instances type to be a random access container
                                auto pet_lhs = extract_expr( lhs );
                                auto container_name = get_container_name_from_iterator( lhs );

                                if ( container_name == "" ) {
                                  report_unsupported_statement_type_with_extra_string( lhs, "could not infer the name of the container from its declaration use RAII" );
                                  return nullptr;
                                }

                                cerr << "container name is " << container_name << endl;

                                auto max_function = container_name + ".size()";
                                auto placeholder = createCallPlaceholder( max_function );

                                // find the size method of the container beeing used 
                                CXXMethodDecl* size_method = nullptr; 
                                if ( auto decl_of_container = dyn_cast_or_null<VarDecl>(decl_ref_expr->getDecl()) ) {
                                        cerr << "got decl of container" << endl;
                                        if ( auto decl_of_container_type = decl_of_container->getType()->getAsCXXRecordDecl() ) {
                                                cerr << "got decl of containers type " << endl;
                                                decl_of_container_type->dump();

                                                size_method = find_size_method( decl_of_container_type );
                                                size_method->dump();
                                        }
                                }
                                if ( !size_method ) return nullptr;

                                cerr << "new id with name " << placeholder << " and size_method " << size_method->getDeclName().getAsString() << endl; 
                                auto id = isl_id_alloc(ctx,  placeholder.c_str(), cast<NamedDecl>(size_method) );
                                auto space = isl_space_alloc(ctx, 0, 0, 0);
                                space = isl_space_set_tuple_id(space, isl_dim_out, id);
                                auto pet_rhs = pet_expr_from_index(isl_multi_pw_aff_zero(space));

#if 0
                                // TODO get type size from <container>.size()
                                auto type_size = 64;
                                auto depth = 1;

                                pet_expr_set_type_size( pet_rhs , type_size );
                                pet_expr_access_set_depth( pet_rhs, depth );
#endif
                                // TODO analyze the return type the the size_method
                                auto return_type = size_method->getReturnType();
                                pet_rhs = extract_access_expr( return_type, pet_rhs );
                                // TODO fill with call to <container>.size()
#if 0
                                unsigned int length = 1000;
                                auto isl_int = isl_val_int_from_ui( ctx, length );
                                auto pet_rhs = pet_expr_new_int( isl_int );
#endif

                                // TODO build a binary expression that compares declref to the iterator
                                //      with container.size() if the loop begins with begin, ends with end and iterates with ++
                                auto op = pet_op_lt;
                                return pet_expr_new_binary(1, op, pet_lhs, pet_rhs);
                        }
                }

                // TODO handle std::end ....

      }
  }
  cerr << "reaching end of " << __PRETTY_FUNCTION__ << " may be an error" << endl;
  return nullptr;
}

// TODO needs information about the iteration direction ? 
// TODO change name to: less then
pet_expr* 
PetScan::build_iterator_unequal_comparison( Expr* lhs, Expr* rhs ) {
	cerr << __PRETTY_FUNCTION__ << endl;
	
	bool is_lhs_it = false;
        if ( auto iterator_decl = isIterator( lhs ) ) {

          cerr << "staring to analyze rhs"<< endl;
          rhs->dump();

          // needed for std::vector
          if ( auto temporary_expression = dyn_cast_or_null<MaterializeTemporaryExpr>( rhs ) ){
            cerr << __LINE__ << endl;
            return build_iterator_less_then_comparison_from_expr( ignoreImplicitCast( temporary_expression->GetTemporaryExpr() ), lhs  );
          }

          // needed for std::array
          if ( auto less_then_comp = build_iterator_less_then_comparison_from_expr( rhs, lhs ) ) {
            return less_then_comp;
          }
    }
	
    cerr << "reached end of " << __PRETTY_FUNCTION__ << " this is maybe an error " << endl;
    return nullptr;
}

/* Construct a pet_expr representing a binary operator expression.
 *
 * If the top level operator is an assignment and the LHS is an access,
 * then we mark that access as a write.  If the operator is a compound
 * assignment, the access is marked as both a read and a write.
 */
__isl_give pet_expr *PetScan::extract_cxx_binary_operator(CXXOperatorCallExpr *expr, OverloadedOperatorKind ook )
{
	std::cerr << __PRETTY_FUNCTION__ << std::endl;
	int type_size;
	pet_expr *lhs, *rhs;

	// convert ook to pet representation

	auto op = OverloadedOperatorKind2pet_op_type(ook);
	if (op == pet_op_last && ook != OO_ExclaimEqual ) {
	  unsupported_msg(expr,string("cannot handle this type is ") + to_string(op) );
	  return nullptr;
	}
	// in the case of a cxx operator call the lhs and rhs 
	// are the first and second function call arguments
	auto arg0 = expr->getArg(0);
	auto arg1 = expr->getArg(1);

	// TODO handle the special case, that a != operator was used to compare two iterators
	if ( ook == OO_ExclaimEqual ) {
		if ( auto binary_operator = build_iterator_unequal_comparison( arg0, arg1 ) ) {
			return binary_operator;
		}
	}
	lhs = extract_expr(arg0);
	rhs = extract_expr(arg1);

	if ( isAssignmentOp( ook ) &&
	    pet_expr_get_type(lhs) == pet_expr_access) {
		lhs = mark_write(lhs);
		if (isCompoundAssignmentOp(ook))
			lhs = pet_expr_access_set_read(lhs, 1);
	}

	type_size = get_type_size(expr->getType(), ast_context);
	cerr << "cxx_binary_operator " << type_size << " " << op << endl;
	return pet_expr_new_binary(type_size, op, lhs, rhs);
}

bool PetScan::isStdContainerIteratorCreator( std::string name ) {
	return name == "begin" || name == "cbegin";
}

VarDecl* PetScan::extract_container_from_instance( Expr* instance, CXXMemberCallExpr* member_call ) {
  if ( auto decl_ref_expr = dyn_cast_or_null<DeclRefExpr>( instance ) ) {
    auto type = decl_ref_expr->getType().getTypePtr();

    auto fd = member_call->getDirectCallee();
    auto name = fd->getDeclName().getAsString();
    cerr << "function called is " << name << endl;

    // TODO if the function is one of the iterator functions and the instance 
    // called is a random access container return the containers decl
    if ( isRandomAccessStlType( type ) && isStdContainerIteratorCreator( name ) ){
      if ( auto var_decl = dyn_cast_or_null<VarDecl>( decl_ref_expr->getDecl() ) ) {
        return var_decl;
      }
    }	
  }else{
    cerr << "not a decl ref expr but:" << endl;
    instance->dump();
  }

  return nullptr;
}

VarDecl* 
PetScan::extract_container_from_expr( Expr* expr ) {
  if ( auto member_call = dyn_cast_or_null<CXXMemberCallExpr>( expr ) ) {
      cerr << "container begin is referenced by a CXXMemberCallExpr" << endl;
      if ( auto instance = member_call->getImplicitObjectArgument() ) {
            cerr << " implicit object argument" << endl;
            return extract_container_from_instance( ignoreImplicitCast(instance), member_call );	
      }
  }else{
      expr->dump();
  }
  cerr << "could not extract the container vardecl from this expr. this may be an error" << endl;
  return nullptr;
}

// if e is a member call expression
// if e is a template function call expression 
// TODO test this with std::begin( constant array ) 
VarDecl* 
PetScan::extract_container( Expr* e ) {
  cerr << __PRETTY_FUNCTION__ << endl;
  e->dump();

  // seams to be needed by std::vector
  // to catch containers referencd via container.begin();
  if ( auto expression_with_cleanups = dyn_cast_or_null<ExprWithCleanups>( e ) ){
          cerr	<< " ewc  " << endl;
          if ( auto construct = dyn_cast_or_null<CXXConstructExpr>( expression_with_cleanups->getSubExpr() ) ) {
                  cerr	<< " ctor  " << endl;
                  if ( auto temporary_expression = dyn_cast_or_null<MaterializeTemporaryExpr> ( construct->getArg(0) ) ) {
                          cerr	<< " te  " << endl;
                          return extract_container_from_expr( ignoreImplicitCast( temporary_expression->GetTemporaryExpr() ) );
                  }
          }
  }

  // is ok for std::array
  if ( auto var_decl = extract_container_from_expr( ignoreImplicitCast(e) ) ) {
    return var_decl;
  }

  cerr << "could not extract the vardecl for the container. this may be an error" << endl;
  return nullptr;
  // to catch containers referenced via std::begin( container ) 
}

// if e is a declRefExpr 
// -> get its declaration 
// -> get its initializer 
// -> extract the referenced container from the initializer
// -> get the decl for this container
// -> build a declRefExpr for this container and return it
DeclRefExpr* 
PetScan::build_base_expression_by_initializer( Expr* e ) {
  cerr << __PRETTY_FUNCTION__ << endl;
  e->dump();
	if ( auto decl_ref_expr = dyn_cast_or_null<DeclRefExpr>( e ) ){
		std::cerr << "is a decl ref expr" << std::endl;
		if ( auto decl = decl_ref_expr->getDecl() ) {
			std::cerr << "has a decl" << std::endl;
			if ( auto var_decl = dyn_cast_or_null<VarDecl>( decl ) ) {
				std::cerr << "is a var decl" << std::endl;
				if ( auto init = var_decl->getInit() ) {
					std::cerr << "has a init" << std::endl;
					if ( auto container = extract_container( init ) ) {
						auto decl_ref_expr = create_DeclRefExpr(container);
						return decl_ref_expr;
					}
				}
			}
		}
	}else{
		std::cerr << "is not a decl ref in build base " << std::endl;
		e->dump();
	}
        cerr << "could not build a base expr. this may be an error" << endl;
	return nullptr;
}

// if e is a declRefExpr 
// -> get its declaration 
DeclRefExpr* 
PetScan::build_index_expression_by_decl( Expr* e ) {
  cerr << __PRETTY_FUNCTION__ << endl;
	if ( auto decl_ref_expr = dyn_cast_or_null<DeclRefExpr>( e ) ){
		std::cerr << "is a decl ref expr" << std::endl;
		return decl_ref_expr;

#if 0
		if ( auto decl = decl_ref_expr->getDecl() ) {
			std::cerr << "has a decl" << std::endl;
			if ( auto var_decl = dyn_cast_or_null<VarDecl>( decl ) ) {
				std::cerr << "is a var decl" << std::endl;
				// now we should have the iterator declaration
				// TODO build a DeclRefExpr that references a integer index variable with the same name

			}
		}
#endif
	}else{
		std::cerr << "is not a decl ref in build index expr" << std::endl;
		e->dump();
	}

	return nullptr;
}

// function to convert a access by a iterator dereference to a normal access of an array
__isl_give pet_expr *PetScan::extract_cxx_unary_operator(CXXOperatorCallExpr *expr, OverloadedOperatorKind ook )
{
	std::cerr << __PRETTY_FUNCTION__ << std::endl;
	int type_size;

	// convert ook to pet representation
	auto op = OverloadedOperatorKind2pet_op_type(ook);

	if (op == pet_op_last ) {
	  unsupported_msg(expr,string("cannot handle this type is ") + to_string(op) );
	  return nullptr;
	}

	auto arg0 = expr->getArg(0);

	
	auto sub_expr = extract_expr(arg0);

	type_size = get_type_size(expr->getType(), ast_context);
	return pet_expr_new_unary(type_size, op, sub_expr);
}


__isl_give pet_expr *PetScan::extract_expr_from_stream(CXXOperatorCallExpr *expr ){
  // TODO check arguments of the call
  // TODO shift operators are read from right to left
  
  if ( expr->getNumArgs() == 2 ) {
    auto stream = expr->getArg(0);
    std::cout << "stream: " << std::endl; 
    stream->dump();

    auto lhs = extract_expr( stream );

    auto element = expr->getArg(1);
    std::cout << "element: " << std::endl;
    element->dump();
    auto rhs = extract_expr(element);

    auto type_size = get_type_size(expr->getType(), ast_context);
    auto ook = expr->getOperator();
    auto op = OverloadedOperatorKind2pet_op_type(ook);

    return pet_expr_new_binary(type_size, op, lhs, rhs);
  }

  std::cout << "could not extract anything from this stream" << std::endl;
  return nullptr;
}

/* Construct a pet_expr representing a CXXOperatorCallExpr.
 */
// TODO issue a warning to tell the user that we assume it has no side effects
__isl_give pet_expr *PetScan::extract_cxx_expr(Expr *op)
{
  std::cerr << __PRETTY_FUNCTION__ << std::endl;
  auto cxx_operator = cast<CXXOperatorCallExpr>(op);
  switch( cxx_operator->getOperator() ){
    case OO_PlusPlus:
      return extract_cxx_unary_operator(cxx_operator, cxx_operator->getOperator());
    case OO_Less:
    case OO_Equal:
      return extract_cxx_binary_operator(cxx_operator,cxx_operator->getOperator());
    case OO_Subscript:
      return extract_access_expr(op);
    case OO_LessLess:
      return extract_expr_from_stream(cxx_operator);
    case OO_Star:
      return extract_access_expr(op);
		case OO_ExclaimEqual:
      return extract_cxx_binary_operator(cxx_operator,cxx_operator->getOperator());
    default:
      unsupported_msg( op , string ("cannot handle this operator: ") + to_string(cxx_operator->getOperator()) );
  }
  return nullptr;
}

/* Construct a pet_expr representing the integer enum constant "ecd".
 */
__isl_give pet_expr *PetScan::extract_expr(MaterializeTemporaryExpr *temp)
{
  auto expr = temp->GetTemporaryExpr();
  return extract_expr( expr );
}


/* Construct a pet_expr representing the integer enum constant "ecd".
 */
__isl_give pet_expr *PetScan::extract_expr(ExprWithCleanups *ewc)
{
  std::cerr << __PRETTY_FUNCTION__ << std::endl;
  auto expr = ewc->getSubExpr();
  return extract_expr( expr );
}


__isl_give pet_expr *PetScan::extract_expr( SubstNonTypeTemplateParmExpr *expr){
  std::cerr << __PRETTY_FUNCTION__ << std::endl;
  auto replacement = expr->getReplacement();
  return extract_expr( replacement );
}

/* Try and construct a pet_expr representing "expr".
 */
__isl_give pet_expr *PetScan::extract_expr(Expr *expr )
{

	//std::cerr << "calling extract_expr hub with type " << expr->getStmtClass()  << std::endl;

	switch (expr->getStmtClass()) {
	case Stmt::UnaryOperatorClass:
		return extract_expr(cast<UnaryOperator>(expr));
	case Stmt::CompoundAssignOperatorClass:
	case Stmt::BinaryOperatorClass:
		return extract_expr(cast<BinaryOperator>(expr));
	case Stmt::ImplicitCastExprClass:
		return extract_expr(cast<ImplicitCastExpr>(expr));
	case Stmt::CXXOperatorCallExprClass:
		return extract_cxx_expr(expr);
	case Stmt::ExprWithCleanupsClass:
		return extract_expr(cast<ExprWithCleanups>(expr));
	case Stmt::ArraySubscriptExprClass:
	case Stmt::StringLiteralClass:
	case Stmt::DeclRefExprClass:
	case Stmt::MemberExprClass:
		return extract_access_expr(expr);
        case Stmt::CXXBoolLiteralExprClass:
                return extract_expr(cast<CXXBoolLiteralExpr>(expr));
	case Stmt::IntegerLiteralClass:
		return extract_expr(cast<IntegerLiteral>(expr));
	case Stmt::FloatingLiteralClass:
		return extract_expr(cast<FloatingLiteral>(expr));
	case Stmt::ParenExprClass:
		return extract_expr(cast<ParenExpr>(expr));
	case Stmt::ConditionalOperatorClass:
		return extract_expr(cast<ConditionalOperator>(expr));
	case Stmt::CallExprClass:{
		return extract_expr(cast<CallExpr>(expr));
	}
	case Stmt::CStyleCastExprClass:
		return extract_expr(cast<CStyleCastExpr>(expr));
	case Stmt::CXXMemberCallExprClass:
		if ( treat_calls_like_access ) {
		  return extract_access_expr( expr );
		}else{
		  return extract_expr(cast<CXXMemberCallExpr>(expr));
		}
	case Stmt::CXXConstructExprClass:
		if ( treat_calls_like_access ) {
		  return extract_access_expr( expr );
		}else{
		  std::cerr << "not implemented" << std::endl;
		  exit(-1);
		  return nullptr;
		}
	case Stmt::MaterializeTemporaryExprClass:
		return extract_expr( cast<MaterializeTemporaryExpr>( expr ) );
	case Stmt::SubstNonTypeTemplateParmExprClass:
		return extract_expr( cast<SubstNonTypeTemplateParmExpr>(expr) );
	default:
		unsupported_msg(expr, string(expr->getStmtClassName()));
	}
	return NULL;
}

/* Check if the given initialization statement is an assignment.
 * If so, return that assignment.  Otherwise return NULL.
 */
BinaryOperator *PetScan::initialization_assignment(Stmt *init)
{
	BinaryOperator *ass;

	if (init->getStmtClass() != Stmt::BinaryOperatorClass)
		return NULL;

	ass = cast<BinaryOperator>(init);
	if (ass->getOpcode() != BO_Assign)
		return NULL;

	return ass;
}

/* Check if the given initialization statement is a declaration
 * of a single variable.
 * If so, return that declaration.  Otherwise return NULL.
 */
Decl *PetScan::initialization_declaration(Stmt *init)
{
	DeclStmt *decl;

	if (init->getStmtClass() != Stmt::DeclStmtClass)
		return NULL;

	decl = cast<DeclStmt>(init);

	if (!decl->isSingleDecl())
		return NULL;

	return decl->getSingleDecl();
}

/* Given the assignment operator in the initialization of a for loop,
 * extract the induction variable, i.e., the (integer)variable being
 * assigned.
 */
ValueDecl *PetScan::extract_induction_variable(BinaryOperator *init)
{
	Expr *lhs;
	DeclRefExpr *ref;
	ValueDecl *decl;
	const Type *type;

	lhs = init->getLHS();
	if (lhs->getStmtClass() != Stmt::DeclRefExprClass) {
		unsupported(init);
		return NULL;
	}

	ref = cast<DeclRefExpr>(lhs);
	decl = ref->getDecl();
	type = decl->getType().getTypePtr();

	if (!type->isIntegerType()) {
		unsupported(lhs);
		return NULL;
	}

	return decl;
}

bool hasAllowedIteratorName( std::string name ) {
  return name == "iterator" || "const_iterator";
}

bool 
PetScan::isIteratorType( const clang::Type* type_ptr ) {
  //std::cerr << "getTypeClassName " << type_ptr->getTypeClassName() << std::endl;
  //std::cerr << "sugared typename " << qt.getAsString() << std::endl;
  
  type_ptr->dump();
  if ( auto typedef_type = dyn_cast_or_null<TypedefType>( type_ptr ) ) {
        
      // check whether the typedef already has the desired name 
      auto typedef_name_declare = typedef_type->getDecl();
      auto name = typedef_name_declare->getNameAsString();
      
      cerr << "typedef_name_declare name " << name << endl;

      if ( hasAllowedIteratorName( name ) ) {
        cerr << "typedef already has the allowed name " << endl;
        return true;
      }

      // call again with desugared type
      return isIteratorType( typedef_type->desugar().getTypePtr() );
  }

  if ( auto elaborated_type = dyn_cast_or_null<ElaboratedType>(type_ptr) ) {
    if ( auto nested_name_specifier = elaborated_type->getQualifier() ) {
			// check for the type beeing vector or array 
			if ( nested_name_specifier->getKind() == NestedNameSpecifier::TypeSpec ) {
				auto type = nested_name_specifier->getAsType();
				if ( isRandomAccessStlType( type ) ) {
					std::cerr << "pet the base type of this iterator is allowed" << std::endl;

					// check the named_type_qt for its name
					auto named_type_qt = elaborated_type->getNamedType();
                                        auto split = named_type_qt.split();
                                        auto type = split.Ty;
                                        type->dump();
                                        if ( auto typedef_type = dyn_cast_or_null<TypedefType>(type)){
                                          if ( auto typedef_type_decl = typedef_type->getDecl() ){
                                            auto qt = typedef_type_decl->getUnderlyingType();
                                            cout << "my name is " << typedef_type_decl->getNameAsString() << endl;
                                            auto name = typedef_type_decl->getNameAsString();
                                            if ( hasAllowedIteratorName( name ) )  {
						std::cerr << "pet: name of the typedef type hiding the iterator is iterator " << std::endl;
						return true;
                                            }
                                          }
                                        }

                                        auto name = named_type_qt.getAsString();
					if ( hasAllowedIteratorName( name ) ) {
						std::cerr << "pet name of the elab types NamedType is iterator " << std::endl;
						return true;
					}else{
						std::cerr << "pet name of the elab types NamedType is not iterator but " << named_type_qt.getAsString() << std::endl;
						return false;
					}
				}
			}else{
				std::cerr << "pet kind is not a TypeSpec but " << nested_name_specifier->getKind() << std::endl;
				return false;
			}
		}
  }else{
    std::cerr << "pet is not a ElaboratedType" << std::endl;
    return false;
  }

  std::cerr << "done " << __PRETTY_FUNCTION__ << std::endl;
  return true;
}

// TODO remove the debug output
bool PetScan::
isIteratorType( QualType qt ){

  // make it query the type we are iterating over
  // if it is a random access type its ok otherwise not

  auto type_ptr = qt.getTypePtr();
	return isIteratorType( type_ptr );
}

/* Given the initialization statement of a for loop and the single
 * declaration in this initialization statement,
 * extract the induction variable, i.e., the (integer) variable being
 * declared.
 */
VarDecl *PetScan::extract_induction_variable(Stmt *init, Decl *decl)
{
	VarDecl *vd;

	vd = cast<VarDecl>(decl);

	const QualType type = vd->getType();
	if (!type->isIntegerType() && !isIteratorType( type ) ) {
		unsupported(init);
		return NULL;
	}

	if (!vd->getInit()) {
		unsupported(init);
		return NULL;
	}

	std::cerr << "pet returning from " << __PRETTY_FUNCTION__ << std::endl;

	return vd;
}

/* Check that op is of the form iv++ or iv--.
 * Return a pet_expr representing "1" or "-1" accordingly.
 */
__isl_give pet_expr *PetScan::extract_unary_increment(
	clang::UnaryOperator *op, clang::ValueDecl *iv)
{
	cerr << __PRETTY_FUNCTION__ << endl;
	Expr *sub;
	DeclRefExpr *ref;
	isl_val *v;

	if (!op->isIncrementDecrementOp()) {
		unsupported(op);
		return NULL;
	}
	cerr << __PRETTY_FUNCTION__ << " " << __LINE__ << endl;

	sub = op->getSubExpr();
	if (sub->getStmtClass() != Stmt::DeclRefExprClass) {
		unsupported(op);
		return NULL;
	}
	cerr << __PRETTY_FUNCTION__ << " " << __LINE__ << endl;

	ref = cast<DeclRefExpr>(sub);
	if (ref->getDecl() != iv) {
		unsupported(op);
		return NULL;
	}
	cerr << __PRETTY_FUNCTION__ << " " << __LINE__ << endl;

	if (op->isIncrementOp())
		v = isl_val_one(ctx);
	else
		v = isl_val_negone(ctx);

	auto ret =  pet_expr_new_int(v);
        cerr << "returning " << ret << endl;
        return ret;
}


// is valid if call is a call to a iterators operator ++ 
__isl_give pet_expr *PetScan::extract_unary_increment( 
		clang::CXXOperatorCallExpr* expr,
		clang::ValueDecl* iv
) {
	cerr << __PRETTY_FUNCTION__ << expr->getNumArgs() << endl;
  auto cxx_operator = expr;
	cxx_operator->dump();

	if ( expr->getNumArgs() != 2 ) return nullptr;
	// check the type of the object beeing used
	auto arg0 = expr->getArg(0);

	cerr << __LINE__ << endl;
	if ( auto decl_ref_expr = dyn_cast_or_null<DeclRefExpr>(ignoreImplicitCast(arg0)) ) {
		cerr << __LINE__ << endl;
		if ( auto decl = decl_ref_expr->getDecl() ) {
			cerr << __LINE__ << endl;
			if ( auto type = decl->getType().getTypePtr() ) {
				cerr << __LINE__ << endl;
				if ( isIteratorType( type ) ) {
					if ( expr->getOperator() == OO_PlusPlus ){
						return pet_expr_new_int(isl_val_one(ctx));
					}
					if ( expr->getOperator() == OO_MinusMinus  ){
						return pet_expr_new_int(isl_val_negone(ctx));
					}
				}
			}
		}
	}

	return nullptr;
}

/* Check if op is of the form
 *
 *	iv = expr
 *
 * and return the increment "expr - iv" as a pet_expr.
 */
__isl_give pet_expr *PetScan::extract_binary_increment(BinaryOperator *op,
	clang::ValueDecl *iv)
{
	cerr << __PRETTY_FUNCTION__ << endl;
	int type_size;
	Expr *lhs;
	DeclRefExpr *ref;
	pet_expr *expr, *expr_iv;

	if (op->getOpcode() != BO_Assign) {
		unsupported(op);
		return NULL;
	}

	lhs = op->getLHS();
	if (lhs->getStmtClass() != Stmt::DeclRefExprClass) {
		unsupported(op);
		return NULL;
	}

	ref = cast<DeclRefExpr>(lhs);
	if (ref->getDecl() != iv) {
		unsupported(op);
		return NULL;
	}

	expr = extract_expr(op->getRHS());

#if 1
	// filter non 1 increment operations
	if ( PetScan::increment_by_one ) {
	  if ( !isIncrementByOne( expr ) ) {
	    unsupported_with_extra_string( op, "pet is restricted to 1 and -1 as loop increment operations" );
	    return nullptr;
	  }
	}
#endif

	expr_iv = extract_expr(lhs);

	type_size = get_type_size(iv->getType(), ast_context);
	return pet_expr_new_binary(type_size, pet_op_sub, expr, expr_iv);
}

// TODO i am not sure about negative one beeing ok for normal scop
bool PetScan::isIncrementByOne( pet_expr* expr ) {
  isl_val* val = pet_expr_int_get_val( expr );
  if ( isl_val_is_one( val ) || isl_val_is_negone(val) ){
    return true;
  }
  return false;
}

/* Check that op is of the form iv += cst or iv -= cst
 * and return a pet_expr corresponding to cst or -cst accordingly.
 */
__isl_give pet_expr *PetScan::extract_compound_increment(
	CompoundAssignOperator *op, clang::ValueDecl *iv)
{
	cerr << __PRETTY_FUNCTION__ << endl;
	Expr *lhs;
	DeclRefExpr *ref;
	bool neg = false;
	pet_expr *expr;
	BinaryOperatorKind opcode;

	opcode = op->getOpcode();
	if (opcode != BO_AddAssign && opcode != BO_SubAssign) {
		unsupported(op);
		return NULL;
	}
	if (opcode == BO_SubAssign)
		neg = true;

	lhs = op->getLHS();
	if (lhs->getStmtClass() != Stmt::DeclRefExprClass) {
		unsupported(op);
		return NULL;
	}

	ref = cast<DeclRefExpr>(lhs);
	if (ref->getDecl() != iv) {
		unsupported(op);
		return NULL;
	}

	expr = extract_expr(op->getRHS());

#if 1
	// filter non 1 increment operations
	if ( PetScan::increment_by_one ) {
	  if ( !isIncrementByOne( expr ) ){
	    unsupported_with_extra_string( op, "pet is restricted to 1 and -1 as loop increment operations" );
	    return nullptr;
	  }
	}
#endif

	if (neg) {
		int type_size;
		type_size = get_type_size(op->getType(), ast_context);
		expr = pet_expr_new_unary(type_size, pet_op_minus, expr);
	}

	return expr;
}

/* Check that the increment of the given for loop increments
 * (or decrements) the induction variable "iv" and return
 * the increment as a pet_expr if successful.
 */
__isl_give pet_expr *PetScan::extract_increment(clang::ForStmt *stmt,
	ValueDecl *iv)
{
	std::cerr << __PRETTY_FUNCTION__ << std::endl;
	Stmt *inc = stmt->getInc();

	if (!inc) {
		report_missing_increment(stmt);
		return NULL;
	}

	if (inc->getStmtClass() == Stmt::UnaryOperatorClass)
		return extract_unary_increment(cast<UnaryOperator>(inc), iv);
	if (inc->getStmtClass() == Stmt::CompoundAssignOperatorClass)
		return extract_compound_increment(
				cast<CompoundAssignOperator>(inc), iv);
	if (inc->getStmtClass() == Stmt::BinaryOperatorClass)
		return extract_binary_increment(cast<BinaryOperator>(inc), iv);

	inc->dump();

	if (inc->getStmtClass() == Stmt::CXXOperatorCallExprClass ) {
	  // TODO issue a warning to warn for side effects
	  return extract_unary_increment( cast<CXXOperatorCallExpr>(inc), iv );
	}

	unsupported(inc);
	std::cerr << "done " <<  __PRETTY_FUNCTION__ << std::endl;
	return NULL;
}

/* Construct a pet_tree for a while loop.
 *
 * If we were only able to extract part of the body, then simply
 * return that part.
 */
__isl_give pet_tree *PetScan::extract(WhileStmt *stmt)
{
	pet_expr *pe_cond;
	pet_tree *tree;

	tree = extract(stmt->getBody());
	if (partial)
		return tree;
	pe_cond = extract_expr(stmt->getCond());
	tree = pet_tree_new_while(pe_cond, tree);

	return tree;
}

__isl_give pet_expr* 
PetScan::build_initializing_expr_from_expr( Expr* expr ) {
  if ( auto cxx_member_call_expr = dyn_cast_or_null<CXXMemberCallExpr>( expr ) ) {
        if ( auto instance = cxx_member_call_expr->getImplicitObjectArgument() ) {
                cerr << __LINE__ << endl;
                // for the case the container was referenced by its instance and .begin()
                if ( auto decl_ref_expr = dyn_cast_or_null<DeclRefExpr>( instance ) ) {
                        cerr << __LINE__ << endl;
                        if ( auto instance_decl = decl_ref_expr->getDecl() ) {
                                cerr << __LINE__ << endl;
                                if ( auto instance_type = instance_decl->getType().getTypePtr() ) {
                                        if ( isRandomAccessStlType( instance_type ) ) {
                                                cerr << __LINE__ << endl;
                                                auto md = cxx_member_call_expr->getDirectCallee();
                                                auto name = md->getDeclName().getAsString();
                                                if ( name == "begin" || name == "cbegin" ) {
                                                        cerr << "name is begin creating a pet expr returning 0" << endl;
                                                        return pet_expr_new_int(isl_val_zero(ctx));
                                                }
                                        }
                                }
                        }
                }
        }
  }
  cerr << "reached end of " << __PRETTY_FUNCTION__ << " this may be an error " << endl;

  return nullptr;
}
// TODO add stuff for std::begin and begin() + 5 ...
pet_expr* 
PetScan::iterator_init_transformation( Expr* rhs ) {
	cerr	<< __PRETTY_FUNCTION__ << endl;
	cerr << "generating replacement code for initialization with calls to begin" << endl;
	rhs->dump();

	if ( auto expr_with_cleanups = dyn_cast_or_null<ExprWithCleanups>( rhs ) ) {
		cerr << __LINE__ << endl;
		if ( auto cxx_construct_expr = dyn_cast_or_null<CXXConstructExpr>( expr_with_cleanups->getSubExpr() ) ) {
			auto n_args = cxx_construct_expr->getNumArgs();
			std::cerr << "cxx_construct_expr n args " << n_args << std::endl;
			if ( auto temporary_expression = dyn_cast_or_null<MaterializeTemporaryExpr>( cxx_construct_expr->getArg(0) ) ) {
			    return build_initializing_expr_from_expr( temporary_expression->GetTemporaryExpr() );
			}
		}
	}

        if ( auto init = build_initializing_expr_from_expr( ignoreImplicitCast(rhs) ) ) {
          return init;
        }

        cerr << "reached end of " << __PRETTY_FUNCTION__ << " this may be an error " << endl;
	return nullptr;	
}

/* Construct a pet_tree for a for statement.
 * The for loop is required to be of one of the following forms
 *
 *	for (i = init; condition; ++i)
 *	for (i = init; condition; --i)
 *	for (i = init; condition; i += constant)
 *	for (i = init; condition; i -= constant)
 *
 * We extract a pet_tree for the body and then include it in a pet_tree
 * of type pet_tree_for.
 *
 * As a special case, we also allow a for loop of the form
 *
 *	for (;;)
 *
 * in which case we return a pet_tree of type pet_tree_infinite_loop.
 *
 * If we were only able to extract part of the body, then simply
 * return that part.
 */
__isl_give pet_tree *PetScan::extract_for(ForStmt *stmt)
{
	std::cerr << __PRETTY_FUNCTION__ << std::endl;
	BinaryOperator *ass;
	Decl *decl;
	Stmt *init;
	Expr *lhs, *rhs;
	ValueDecl *iv;
	pet_tree *tree;
	struct pet_scop *scop;
	int independent;
	int declared;
	pet_expr *pe_init = nullptr, *pe_inc, *pe_iv, *pe_cond;

	independent = is_current_stmt_marked_independent();

	if (!stmt->getInit() && !stmt->getCond() && !stmt->getInc()) {
		tree = extract(stmt->getBody());
		if (partial)
			return tree;
		tree = pet_tree_new_infinite_loop(tree);
		return tree;
	}

	init = stmt->getInit();
	if (!init) {
		unsupported(stmt);
		return NULL;
	}
	if ((ass = initialization_assignment(init)) != NULL) {
		iv = extract_induction_variable(ass);
		if (!iv)
			return NULL;
		lhs = ass->getLHS();
		rhs = ass->getRHS();
	} else if ((decl = initialization_declaration(init)) != NULL) {
		VarDecl *var = extract_induction_variable(init, decl);
		if (!var)
			return NULL;
		iv = var;
		rhs = var->getInit();
		lhs = create_DeclRefExpr(var);
	} else {
		unsupported(stmt->getInit());
		return NULL;
	}

	declared = !initialization_assignment(stmt->getInit());
	cerr << "extract information from body " << endl;
	tree = extract(stmt->getBody());
	cerr << "body done" << endl;

	// lets see what it understood
	pet_tree_dump( tree );

	if (partial)
		return tree;
	std::cerr << "pe_iv extraction" << std::endl;
	pe_iv = extract_access_expr(iv);
	pet_expr_dump(pe_iv);
	std::cerr << "done pe_iv extraction" << std::endl;
	pe_iv = mark_write(pe_iv);

	treat_calls_like_access = true;
	std::cerr << "pe_init extraction" << std::endl;
	if ( auto iterator_init = iterator_init_transformation( rhs ) ) {
		pe_init = iterator_init;
	}else{
		pe_init = extract_expr(rhs);
	}
	cerr	<< "init " << pe_init << endl;
	pet_expr_dump(pe_init);
	std::cerr << "done pe_init extraction" << std::endl;
	treat_calls_like_access = false;

	if (!stmt->getCond())
		pe_cond = pet_expr_new_int(isl_val_one(ctx));
	else{
	  treat_calls_like_access = true;
	  pe_cond = extract_expr(stmt->getCond());
		cerr	<< "cond " << pe_cond << endl;
	  treat_calls_like_access = false;
	}
	
	std::cerr << "after cond extraction" << std::endl;
	pe_inc = extract_increment(stmt, iv);

        cerr << pe_iv << " " << pe_init << " " << pe_cond << " " << pe_inc << " " << tree << endl; 

	tree = pet_tree_new_for(independent, declared, pe_iv, pe_init, pe_cond,
				pe_inc, tree);
	pet_tree_dump( tree );
	std::cerr << "done " <<  __PRETTY_FUNCTION__ << " tree " << tree << std::endl;
	return tree;
}


// TODO continue canonicalize this to a normal loop via index
__isl_give pet_tree *PetScan::extract_range_for(CXXForRangeStmt *stmt)
{
	std::cerr << __PRETTY_FUNCTION__ << std::endl;
	BinaryOperator *ass;
	Decl *decl;
	Stmt *init;
	Expr *lhs, *rhs;
	ValueDecl *iv;
	pet_tree *tree;
	struct pet_scop *scop;
	int independent;
	int declared;
	pet_expr *pe_init, *pe_inc, *pe_iv, *pe_cond;

	independent = is_current_stmt_marked_independent();

	init = stmt->getRangeInit();
	if (!init) {
          unsupported(stmt);
          return NULL;
	}

#if 0
	if ((ass = initialization_assignment(init)) != NULL) {
		iv = extract_induction_variable(ass);
		if (!iv)
			return NULL;
		lhs = ass->getLHS();
		rhs = ass->getRHS();
	} else if ((decl = initialization_declaration(init)) != NULL) {
		VarDecl *var = extract_induction_variable(init, decl);
		if (!var)
			return NULL;
		iv = var;
		rhs = var->getInit();
		lhs = create_DeclRefExpr(var);
	} else {
		unsupported(stmt->getInit());
		return NULL;
	}

	declared = !initialization_assignment(stmt->getInit());
	tree = extract(stmt->getBody());

	// lets see what it understood
	pet_tree_dump( tree );

	if (partial)
		return tree;
	std::cerr << "pe_iv extraction" << std::endl;
	pe_iv = extract_access_expr(iv);
	std::cerr << "done pe_iv extraction" << std::endl;
	pe_iv = mark_write(pe_iv);

	treat_calls_like_access = true;
	pe_init = extract_expr(rhs);
	treat_calls_like_access = false;

	if (!stmt->getCond())
		pe_cond = pet_expr_new_int(isl_val_one(ctx));
	else{
	  treat_calls_like_access = true;
	  pe_cond = extract_expr(stmt->getCond());
	  treat_calls_like_access = false;
	}
	
	std::cerr << "after cond extraction" << std::endl;
	pe_inc = extract_increment(stmt, iv);
	tree = pet_tree_new_for(independent, declared, pe_iv, pe_init, pe_cond,
				pe_inc, tree);
	std::cerr << "done " <<  __PRETTY_FUNCTION__ << std::endl;
#endif
	return tree;
}



/* Try and construct a pet_tree corresponding to a compound statement.
 *
 * "skip_declarations" is set if we should skip initial declarations
 * in the children of the compound statements.
 */
__isl_give pet_tree *PetScan::extract(CompoundStmt *stmt,
	bool skip_declarations)
{
	return extract(stmt->children(), true, skip_declarations);
}

/* Return the file offset of the expansion location of "Loc".
 */
static unsigned getExpansionOffset(SourceManager &SM, SourceLocation Loc)
{
	return SM.getFileOffset(SM.getExpansionLoc(Loc));
}

#if 1

/* Return a SourceLocation for the location after the first semicolon
 * after "loc".  If Lexer::findLocationAfterToken is available, we simply
 * call it and also skip trailing spaces and newline.
 */
static SourceLocation location_after_semi(SourceLocation loc, SourceManager &SM,
	const LangOptions &LO)
{
	return Lexer::findLocationAfterToken(loc, tok::semi, SM, LO, true);
}

#else

/* Return a SourceLocation for the location after the first semicolon
 * after "loc".  If Lexer::findLocationAfterToken is not available,
 * we look in the underlying character data for the first semicolon.
 */
static SourceLocation location_after_semi(SourceLocation loc, SourceManager &SM,
	const LangOptions &LO)
{
	const char *semi;
	const char *s = SM.getCharacterData(loc);

	semi = strchr(s, ';');
	if (!semi)
		return SourceLocation();
	return loc.getFileLocWithOffset(semi + 1 - s);
}

#endif

/* If the token at "loc" is the first token on the line, then return
 * a location referring to the start of the line and set *indent
 * to the indentation of "loc"
 * Otherwise, return "loc" and set *indent to "".
 *
 * This function is used to extend a scop to the start of the line
 * if the first token of the scop is also the first token on the line.
 *
 * We look for the first token on the line.  If its location is equal to "loc",
 * then the latter is the location of the first token on the line.
 */
static SourceLocation move_to_start_of_line_if_first_token(SourceLocation loc,
	SourceManager &SM, const LangOptions &LO, char **indent)
{
	std::pair<FileID, unsigned> file_offset_pair;
	llvm::StringRef file;
	const char *pos;
	Token tok;
	SourceLocation token_loc, line_loc;
	int col;
	const char *s;

	loc = SM.getExpansionLoc(loc);
	col = SM.getExpansionColumnNumber(loc);
	line_loc = loc.getLocWithOffset(1 - col);
	file_offset_pair = SM.getDecomposedLoc(line_loc);
	file = SM.getBufferData(file_offset_pair.first, NULL);
	pos = file.data() + file_offset_pair.second;

	Lexer lexer(SM.getLocForStartOfFile(file_offset_pair.first), LO,
					file.begin(), pos, file.end());
	lexer.LexFromRawLexer(tok);
	token_loc = tok.getLocation();

	s = SM.getCharacterData(line_loc);
	*indent = strndup(s, token_loc == loc ? col - 1 : 0);

	if (token_loc == loc)
		return line_loc;
	else
		return loc;
}

/* Construct a pet_loc corresponding to the region covered by "range".
 * If "skip_semi" is set, then we assume "range" is followed by
 * a semicolon and also include this semicolon.
 */
__isl_give pet_loc *PetScan::construct_pet_loc(SourceRange range,
	bool skip_semi)
{
	SourceLocation loc = range.getBegin();
	SourceManager &SM = ast_context.getSourceManager();
	const LangOptions &LO = ast_context.getLangOpts();
	int line = ast_context.getSourceManager().getExpansionLineNumber(loc);
	unsigned start, end;
	char *indent;

	loc = move_to_start_of_line_if_first_token(loc, SM, LO, &indent);
	start = getExpansionOffset(SM, loc);
	loc = range.getEnd();
	if (skip_semi)
		loc = location_after_semi(loc, SM, LO);
	else
		loc = Lexer::getLocForEndOfToken(loc,0,SM,LO);
	end = getExpansionOffset(SM, loc);

	return pet_loc_alloc(ctx, start, end, line, indent);
}

/* Convert a top-level pet_expr to an expression pet_tree.
 */
__isl_give pet_tree *PetScan::extract(__isl_take pet_expr *expr,
	SourceRange range, bool skip_semi)
{
	pet_loc *loc;
	pet_tree *tree;

	tree = pet_tree_new_expr(expr);
	loc = construct_pet_loc(range, skip_semi);
	tree = pet_tree_set_loc(tree, loc);

	return tree;
}

/* Construct a pet_tree for an if statement.
 */
__isl_give pet_tree *PetScan::extract(IfStmt *stmt)
{
	pet_expr *pe_cond;
	pet_tree *tree, *tree_else;
	struct pet_scop *scop;
	int int_size;

	pe_cond = extract_expr(stmt->getCond());
	tree = extract(stmt->getThen());
	if (stmt->getElse()) {
		tree_else = extract(stmt->getElse());
		if (options->autodetect) {
			if (tree && !tree_else) {
				partial = true;
				pet_expr_free(pe_cond);
				return tree;
			}
			if (!tree && tree_else) {
				partial = true;
				pet_expr_free(pe_cond);
				return tree_else;
			}
		}
		tree = pet_tree_new_if_else(pe_cond, tree, tree_else);
	} else
		tree = pet_tree_new_if(pe_cond, tree);
	return tree;
}

/* Try and construct a pet_tree for a label statement.
 */
__isl_give pet_tree *PetScan::extract(LabelStmt *stmt)
{
	isl_id *label;
	pet_tree *tree;

	label = isl_id_alloc(ctx, stmt->getName(), NULL);

	tree = extract(stmt->getSubStmt());
	tree = pet_tree_set_label(tree, label);
	return tree;
}

/* Update the location of "tree" to include the source range of "stmt".
 *
 * Actually, we create a new location based on the source range of "stmt" and
 * then extend this new location to include the region of the original location.
 * This ensures that the line number of the final location refers to "stmt".
 */
__isl_give pet_tree *PetScan::update_loc(__isl_take pet_tree *tree, Stmt *stmt)
{
	pet_loc *loc, *tree_loc;

	tree_loc = pet_tree_get_loc(tree);
	loc = construct_pet_loc(stmt->getSourceRange(), false);
	loc = pet_loc_update_start_end_from_loc(loc, tree_loc);
	pet_loc_free(tree_loc);

	tree = pet_tree_set_loc(tree, loc);
	return tree;
}


// extract the expression that would be returned by this statement 
// since we are just interested in the possible influence of return on function calls
// TODO check that this is not possible in loops but just in function summaries
__isl_give pet_tree *PetScan::extract(clang::ReturnStmt *expr){
  auto ret = expr->getRetValue();
  return extract(ret);
}

/* Try and construct a pet_tree corresponding to "stmt".
 *
 * If "stmt" is a compound statement, then "skip_declarations"
 * indicates whether we should skip initial declarations in the
 * compound statement.
 *
 * If the constructed pet_tree is not a (possibly) partial representation
 * of "stmt", we update start and end of the pet_scop to those of "stmt".
 * In particular, if skip_declarations is set, then we may have skipped
 * declarations inside "stmt" and so the pet_scop may not represent
 * the entire "stmt".
 * Note that this function may be called with "stmt" referring to the entire
 * body of the function, including the outer braces.  In such cases,
 * skip_declarations will be set and the braces will not be taken into
 * account in tree->loc.
 */
__isl_give pet_tree *PetScan::extract(Stmt *stmt, bool skip_declarations)
{
	pet_tree *tree;

	set_current_stmt(stmt);

	if (isa<Expr>(stmt))
		return extract(extract_expr(cast<Expr>(stmt)),
				stmt->getSourceRange(), true);

	switch (stmt->getStmtClass()) {
	case Stmt::WhileStmtClass:
		tree = extract(cast<WhileStmt>(stmt));
		break;
	case Stmt::ForStmtClass:
		tree = extract_for(cast<ForStmt>(stmt));
		break;
	case Stmt::CXXForRangeStmtClass:
		tree = extract_range_for(cast<CXXForRangeStmt>(stmt));
		break;
	case Stmt::IfStmtClass:
		tree = extract(cast<IfStmt>(stmt));
		break;
	case Stmt::CompoundStmtClass:
		tree = extract(cast<CompoundStmt>(stmt), skip_declarations);
		break;
	case Stmt::LabelStmtClass:
		tree = extract(cast<LabelStmt>(stmt));
		break;
	case Stmt::ContinueStmtClass:
		tree = pet_tree_new_continue(ctx);
		break;
	case Stmt::BreakStmtClass:
		tree = pet_tree_new_break(ctx);
		break;
	case Stmt::DeclStmtClass:
		tree = extract(cast<DeclStmt>(stmt));
		std::cerr << "tree for decl stmt " << tree << std::endl;
		break;
        case Stmt::ReturnStmtClass:
                tree = extract(cast<ReturnStmt>(stmt));
                break;
	default:
		report_unsupported_statement_type(stmt);
		return NULL;
	}

	if (partial || skip_declarations)
		return tree;

	return update_loc(tree, stmt);
}

/* Given a sequence of statements "stmt_range" of which the first "n_decl"
 * are declarations and of which the remaining statements are represented
 * by "tree", try and extend "tree" to include the last sequence of
 * the initial declarations that can be completely extracted.
 *
 * We start collecting the initial declarations and start over
 * whenever we come across a declaration that we cannot extract.
 * If we have been able to extract any declarations, then we
 * copy over the contents of "tree" at the end of the declarations.
 * Otherwise, we simply return the original "tree".
 */
__isl_give pet_tree *PetScan::insert_initial_declarations(
	__isl_take pet_tree *tree, int n_decl, StmtRange stmt_range)
{
	StmtIterator i;
	pet_tree *res;
	int n_stmt;
	int is_block;
	int j;

	n_stmt = pet_tree_block_n_child(tree);
	is_block = pet_tree_block_get_block(tree);
	res = pet_tree_new_block(ctx, is_block, n_decl + n_stmt);

	for (i = stmt_range.begin(); n_decl; ++i, --n_decl) {
		Stmt *child = *i;
		pet_tree *tree_i;

		tree_i = extract(child);
		if (tree_i && !partial) {
			res = pet_tree_block_add_child(res, tree_i);
			continue;
		}
		pet_tree_free(tree_i);
		partial = false;
		if (pet_tree_block_n_child(res) == 0)
			continue;
		pet_tree_free(res);
		res = pet_tree_new_block(ctx, is_block, n_decl + n_stmt);
	}

	if (pet_tree_block_n_child(res) == 0) {
		pet_tree_free(res);
		return tree;
	}

	for (j = 0; j < n_stmt; ++j) {
		pet_tree *tree_i;

		tree_i = pet_tree_block_get_child(tree, j);
		res = pet_tree_block_add_child(res, tree_i);
	}
	pet_tree_free(tree);

	return res;
}

/* Try and construct a pet_tree corresponding to (part of)
 * a sequence of statements.
 *
 * "block" is set if the sequence represents the children of
 * a compound statement.
 * "skip_declarations" is set if we should skip initial declarations
 * in the sequence of statements.
 *
 * If autodetect is set, then we allow the extraction of only a subrange
 * of the sequence of statements.  However, if there is at least one
 * kill and there is some subsequent statement for which we could not
 * construct a tree, then turn off the "block" property of the tree
 * such that no extra kill will be introduced at the end of the (partial)
 * block.  If, on the other hand, the final range contains
 * no statements, then we discard the entire range.
 *
 * If the entire range was extracted, apart from some initial declarations,
 * then we try and extend the range with the latest of those initial
 * declarations.
 */
__isl_give pet_tree *PetScan::extract(StmtRange stmt_range, bool block,
	bool skip_declarations)
{
	StmtIterator i;
	int j, skip;
	bool has_kills = false;
	bool partial_range = false;
	pet_tree *tree;

	for (i = stmt_range.begin(), j = 0; i != stmt_range.end(); ++i, ++j)
		;

	tree = pet_tree_new_block(ctx, block, j);

	skip = 0;
	i = stmt_range.begin();
	if (skip_declarations)
		for (; i != stmt_range.end(); ++i) {
			if ((*i)->getStmtClass() != Stmt::DeclStmtClass)
				break;
			++skip;
		}

	for (; i != stmt_range.end(); ++i) {
		Stmt *child = *i;
		pet_tree *tree_i;

		tree_i = extract(child);
		if (pet_tree_block_n_child(tree) != 0 && partial) {
			pet_tree_free(tree_i);
			break;
		}
		if (tree_i && child->getStmtClass() == Stmt::DeclStmtClass &&
		    block)
			has_kills = true;
		if (options->autodetect) {
			if (tree_i)
				tree = pet_tree_block_add_child(tree, tree_i);
			else
				partial_range = true;
			if (pet_tree_block_n_child(tree) != 0 && !tree_i)
				partial = true;
		} else {
			tree = pet_tree_block_add_child(tree, tree_i);
		}

		if (partial || !tree)
			break;
	}

	if (!tree)
		return NULL;

	if (partial) {
		if (has_kills)
			tree = pet_tree_block_set_block(tree, 0);
	} else if (partial_range) {
		if (pet_tree_block_n_child(tree) == 0) {
			pet_tree_free(tree);
			return NULL;
		}
		partial = true;
	} else if (skip > 0)
		tree = insert_initial_declarations(tree, skip, stmt_range);

	return tree;
}

/* Is "T" the type of a variable length array with static size?
 */
static bool is_vla_with_static_size(QualType T)
{
	const VariableArrayType *vlatype;

	if (!T->isVariableArrayType())
		return false;
	vlatype = cast<VariableArrayType>(T);
	return vlatype->getSizeModifier() == VariableArrayType::Static;
}

/* Return the type of "decl" as an array.
 *
 * In particular, if "decl" is a parameter declaration that
 * is a variable length array with a static size, then
 * return the original type (i.e., the variable length array).
 * Otherwise, return the type of decl.
 */
static QualType get_array_type(ValueDecl *decl)
{
	ParmVarDecl *parm;
	QualType T;

	parm = dyn_cast<ParmVarDecl>(decl);
	if (!parm)
		return decl->getType();

	T = parm->getOriginalType();
	if (!is_vla_with_static_size(T))
		return decl->getType();
	return T;
}

extern "C" {
	static __isl_give pet_expr *get_array_size(__isl_keep pet_expr *access,
		void *user);
	static struct pet_array *extract_array(__isl_keep pet_expr *access,
		__isl_keep pet_context *pc, void *user);
}

/* Construct a pet_expr that holds the sizes of the array accessed
 * by "access".
 * This function is used as a callback to pet_context_add_parameters,
 * which is also passed a pointer to the PetScan object.
 */
static __isl_give pet_expr *get_array_size(__isl_keep pet_expr *access,
	void *user)
{
	PetScan *ps = (PetScan *) user;
	isl_id *id;
	ValueDecl *decl;
	const Type *type;

	id = pet_expr_access_get_id(access);

	auto user_data = isl_id_get_user(id);
	auto udtype = get_isl_id_user_data_type( user_data );
	if ( udtype == ITI_NamedDecl || udtype == ITI_Unknown ){
	  decl = (ValueDecl *) isl_id_get_user(id);
	  isl_id_free(id);
	  type = get_array_type(decl).getTypePtr();
	  return ps->get_array_size(type);
	}
	if ( udtype == ITI_StringLiteral ) {
	  auto slit = (StringLiteral*)user_data;
	  isl_id_free(id);
	  ps->get_array_size(slit);
	}
}

/* Construct and return a pet_array corresponding to the variable
 * accessed by "access".
 * This function is used as a callback to pet_scop_from_pet_tree,
 * which is also passed a pointer to the PetScan object.
 */
static struct pet_array *extract_array(__isl_keep pet_expr *access,
	__isl_keep pet_context *pc, void *user)
{
	PetScan *ps = (PetScan *) user;
	isl_ctx *ctx;
	isl_id *id;
	ValueDecl *iv;

	ctx = pet_expr_get_ctx(access);
	id = pet_expr_access_get_id(access);
	iv = (ValueDecl *) isl_id_get_user(id);
	isl_id_free(id);
	return ps->extract_array(ctx, iv, NULL, pc);
}

/* Extract a function summary from the body of "fd".
 *
 * We extract a scop from the function body in a context with as
 * parameters the integer arguments of the function.
 * We turn off autodetection (in case it was set) to ensure that
 * the entire function body is considered.
 * We then collect the accessed array elements and attach them
 * to the corresponding array arguments, taking into account
 * that the function body may access members of array elements.
 *
 * The reason for representing the integer arguments as parameters in
 * the context is that if we were to instead start with a context
 * with the function arguments as initial dimensions, then we would not
 * be able to refer to them from the array extents, without turning
 * array extents into maps.
 *
 * The result is stored in the summary_cache cache so that we can reuse
 * it if this method gets called on the same function again later on.
 */
__isl_give pet_function_summary *PetScan::get_summary(FunctionDecl *fd)
{
  cerr << __PRETTY_FUNCTION__ << endl;
	isl_space *space;
	isl_set *domain;
	pet_context *pc;
	pet_tree *tree;
	pet_function_summary *summary;
	unsigned n;
	ScopLoc loc;
	int save_autodetect;
	struct pet_scop *scop;
	int int_size;
	isl_union_set *may_read, *may_write, *must_write;
	isl_union_map *to_inner;

	if (summary_cache.find(fd) != summary_cache.end())
		return pet_function_summary_copy(summary_cache[fd]);

	space = isl_space_set_alloc(ctx, 0, 0);

	fd->dumpColor();
	n = fd->getNumParams();
	std::cerr << "n parameters " << n << std::endl;
	std::cerr << "is variadic? " << fd->isVariadic() << std::endl;

	// TODO if the function is variadic it is not possible to determin all parameters

	summary = pet_function_summary_alloc(ctx, n);

	if ( fd->isVariadic() ){
	  summary = pet_function_summary_set_variadic( summary );
	}
	for (int i = 0; i < n; ++i) {
		ParmVarDecl *parm = fd->getParamDecl(i);
		QualType type = parm->getType();
		isl_id *id;

		if (!type->isIntegerType())
			continue;
		id = create_decl_id(ctx, parm);
		space = isl_space_insert_dims(space, isl_dim_param, 0, 1);
		space = isl_space_set_dim_id(space, isl_dim_param, 0,
						isl_id_copy(id));
		summary = pet_function_summary_set_int(summary, i, id);
	}

	save_autodetect = options->autodetect;
	options->autodetect = 0;
	PetScan body_scan( ast_context, loc, options,
				isl_union_map_copy(value_bounds), independent);

	tree = body_scan.extract(fd->getBody(), false);

	domain = isl_set_universe(space);
	pc = pet_context_alloc(domain);
	pc = pet_context_add_parameters(pc, tree,
						&::get_array_size, &body_scan);
	int_size = size_in_bytes(ast_context, ast_context.IntTy);
	scop = pet_scop_from_pet_tree(tree, int_size,
					&::extract_array, &body_scan, pc);
	std::cerr << __FILE__ << " " << __LINE__ << std::endl;
	scop = scan_arrays(scop, pc);
	may_read = isl_union_map_range(pet_scop_collect_may_reads(scop));
	may_write = isl_union_map_range(pet_scop_collect_may_writes(scop));
	must_write = isl_union_map_range(pet_scop_collect_must_writes(scop));
	to_inner = pet_scop_compute_outer_to_inner(scop);
	pet_scop_free(scop);
	std::cerr << __FILE__ << " " << __LINE__ << std::endl;

	for (int i = 0; i < n; ++i) {
		ParmVarDecl *parm = fd->getParamDecl(i);
		QualType type = parm->getType();
		struct pet_array *array;
		isl_space *space;
		isl_union_set *data_set;
		isl_union_set *may_read_i, *may_write_i, *must_write_i;

		if (array_depth(type.getTypePtr()) == 0)
			continue;

		array = body_scan.extract_array(ctx, parm, NULL, pc);
		space = array ? isl_set_get_space(array->extent) : NULL;
		pet_array_free(array);
		data_set = isl_union_set_from_set(isl_set_universe(space));
		data_set = isl_union_set_apply(data_set,
					isl_union_map_copy(to_inner));
		may_read_i = isl_union_set_intersect(
				isl_union_set_copy(may_read),
				isl_union_set_copy(data_set));
		may_write_i = isl_union_set_intersect(
				isl_union_set_copy(may_write),
				isl_union_set_copy(data_set));
		must_write_i = isl_union_set_intersect(
				isl_union_set_copy(must_write), data_set);
		summary = pet_function_summary_set_array(summary, i,
				may_read_i, may_write_i, must_write_i);
	}
	std::cerr << __FILE__ << " " << __LINE__ << std::endl;

	isl_union_set_free(may_read);
	isl_union_set_free(may_write);
	isl_union_set_free(must_write);
	isl_union_map_free(to_inner);

	options->autodetect = save_autodetect;
	pet_context_free(pc);

	summary_cache[fd] = pet_function_summary_copy(summary);
	std::cerr << __FILE__ << " " << __LINE__ << std::endl;

	return summary;
}

/* If "fd" has a function body, then extract a function summary from
 * this body and attach it to the call expression "expr".
 *
 * Even if a function body is available, "fd" itself may point
 * to a declaration without function body.  We therefore first
 * replace it by the declaration that comes with a body (if any).
 *
 * It is not clear why hasBody takes a reference to a const FunctionDecl *.
 * It seems that it is possible to directly use the iterators to obtain
 * a non-const pointer.
 * Since we are not going to use the pointer to modify anything anyway,
 * it seems safe to drop the constness.  The alternative would be to
 * modify a lot of other functions to include const qualifiers.
 */
__isl_give pet_expr *PetScan::set_summary(__isl_take pet_expr *expr,
	FunctionDecl *fd)
{
	pet_function_summary *summary;
	const FunctionDecl *def;

	if (!expr)
		return NULL;
	if (!fd->hasBody(def))
		return expr;

	fd = const_cast<FunctionDecl *>(def);

	summary = get_summary(fd);

	expr = pet_expr_call_set_summary(expr, summary);

	return expr;
}

/* Extract a pet_scop from "tree".
 *
 * We simply call pet_scop_from_pet_tree with the appropriate arguments and
 * then add pet_arrays for all accessed arrays.
 * We populate the pet_context with assignments for all parameters used
 * inside "tree" or any of the size expressions for the arrays accessed
 * by "tree" so that they can be used in affine expressions.
 */
struct pet_scop *PetScan::extract_scop(__isl_take pet_tree *tree)
{
	int int_size;
	isl_set *domain;
	pet_context *pc;
	pet_scop *scop;

	int_size = size_in_bytes(ast_context, ast_context.IntTy);

	domain = isl_set_universe(isl_space_set_alloc(ctx, 0, 0));
	pc = pet_context_alloc(domain);
	pc = pet_context_add_parameters(pc, tree, &::get_array_size, this);

	std::cerr << __FILE__ << " " << __LINE__ << std::endl;
	scop = pet_scop_from_pet_tree(tree, int_size,
					&::extract_array, this, pc);
	std::cerr << __FILE__ << " " << __LINE__ << std::endl;
	scop = scan_arrays(scop, pc);
	std::cerr << __FILE__ << " " << __LINE__ << std::endl;
	pet_context_free(pc);
	std::cerr << __FILE__ << " " << __LINE__ << std::endl;

        cerr << "returing scop " << scop << endl;
	return scop;
}

/* Check if the scop marked by the user is exactly this Stmt
 * or part of this Stmt.
 * If so, return a pet_scop corresponding to the marked region.
 * Otherwise, return NULL.
 */
struct pet_scop *PetScan::scan(Stmt *stmt)
{
	SourceManager &SM = ast_context.getSourceManager();
	unsigned start_off, end_off;

	start_off = getExpansionOffset(SM, stmt->getLocStart());
	end_off = getExpansionOffset(SM, stmt->getLocEnd());

	if (start_off > loc.end)
		return NULL;
	if (end_off < loc.start)
		return NULL;

	if (start_off >= loc.start && end_off <= loc.end)
		return extract_scop(extract(stmt));

	StmtIterator start;
	for (start = stmt->child_begin(); start != stmt->child_end(); ++start) {
		Stmt *child = *start;
		if (!child)
			continue;
		start_off = getExpansionOffset(SM, child->getLocStart());
		end_off = getExpansionOffset(SM, child->getLocEnd());
		if (start_off < loc.start && end_off >= loc.end)
			return scan(child);
		if (start_off >= loc.start)
			break;
	}

	StmtIterator end;
	for (end = start; end != stmt->child_end(); ++end) {
		Stmt *child = *end;
		start_off = SM.getFileOffset(child->getLocStart());
		if (start_off >= loc.end)
			break;
	}

	return extract_scop(extract(StmtRange(start, end), false, false));
}

/* Set the size of index "pos" of "array" to "size".
 * In particular, add a constraint of the form
 *
 *	i_pos < size
 *
 * to array->extent and a constraint of the form
 *
 *	size >= 0
 *
 * to array->context.
 *
 * The domain of "size" is assumed to be zero-dimensional.
 */
static struct pet_array *update_size(struct pet_array *array, int pos,
	__isl_take isl_pw_aff *size)
{
	isl_set *valid;
	isl_set *univ;
	isl_set *bound;
	isl_space *dim;
	isl_aff *aff;
	isl_pw_aff *index;
	isl_id *id;

	if (!array)
		goto error;

	valid = isl_set_params(isl_pw_aff_nonneg_set(isl_pw_aff_copy(size)));
	array->context = isl_set_intersect(array->context, valid);

	dim = isl_set_get_space(array->extent);
	aff = isl_aff_zero_on_domain(isl_local_space_from_space(dim));
	aff = isl_aff_add_coefficient_si(aff, isl_dim_in, pos, 1);
	univ = isl_set_universe(isl_aff_get_domain_space(aff));
	index = isl_pw_aff_alloc(univ, aff);

	size = isl_pw_aff_add_dims(size, isl_dim_in,
				isl_set_dim(array->extent, isl_dim_set));
	id = isl_set_get_tuple_id(array->extent);
	size = isl_pw_aff_set_tuple_id(size, isl_dim_in, id);
	bound = isl_pw_aff_lt_set(index, size);

	array->extent = isl_set_intersect(array->extent, bound);

	if (!array->context || !array->extent)
		return pet_array_free(array);

	return array;
error:
	isl_pw_aff_free(size);
	return NULL;
}

#ifdef HAVE_DECAYEDTYPE

/* If "type" is a decayed type, then set *decayed to true and
 * return the original type.
 */
static const Type *undecay(const Type *type, bool *decayed)
{
	*decayed = isa<DecayedType>(type);
	if (*decayed)
		type = cast<DecayedType>(type)->getOriginalType().getTypePtr();
	return type;
}

#else

/* If "type" is a decayed type, then set *decayed to true and
 * return the original type.
 * Since this version of clang does not define a DecayedType,
 * we cannot obtain the original type even if it had been decayed and
 * we set *decayed to false.
 */
static const Type *undecay(const Type *type, bool *decayed)
{
	*decayed = false;
	return type;
}

#endif

/* Figure out the size of the array at position "pos" and all
 * subsequent positions from "type" and update the corresponding
 * argument of "expr" accordingly.
 *
 * The initial type (when pos is zero) may be a pointer type decayed
 * from an array type, if this initial type is the type of a function
 * argument.  This only happens if the original array type has
 * a constant size in the outer dimension as otherwise we get
 * a VariableArrayType.  Try and obtain this original type (if available) and
 * take the outer array size into account if it was marked static.
 */
__isl_give pet_expr *PetScan::set_upper_bounds(__isl_take pet_expr *expr,
	const Type *type, int pos)
{
	const ArrayType *atype;
	pet_expr *size;
	bool decayed = false;

	if (!expr)
		return NULL;

	if (pos == 0)
		type = undecay(type, &decayed);

	if (type->isPointerType()) {
		type = type->getPointeeType().getTypePtr();
		return set_upper_bounds(expr, type, pos + 1);
	}
	if (!type->isArrayType())
		return expr;

	type = type->getCanonicalTypeInternal().getTypePtr();
	atype = cast<ArrayType>(type);

	if (decayed && atype->getSizeModifier() != ArrayType::Static) {
		type = atype->getElementType().getTypePtr();
		return set_upper_bounds(expr, type, pos + 1);
	}

	if (type->isConstantArrayType()) {
		const ConstantArrayType *ca = cast<ConstantArrayType>(atype);
		size = extract_expr(ca->getSize());
		expr = pet_expr_set_arg(expr, pos, size);
	} else if (type->isVariableArrayType()) {
		const VariableArrayType *vla = cast<VariableArrayType>(atype);
		size = extract_expr(vla->getSizeExpr());
		expr = pet_expr_set_arg(expr, pos, size);
	}

	type = atype->getElementType().getTypePtr();

	return set_upper_bounds(expr, type, pos + 1);
}

__isl_give pet_expr *PetScan::set_upper_bounds(__isl_take pet_expr *expr, const StringLiteral* slit)
{
	if (!expr)
		return NULL;

	// is kind of a constant array type
	unsigned int length = slit->getLength();
	auto isl_int = isl_val_int_from_ui( ctx, length );
	auto pet_length = pet_expr_new_int( isl_int );
	expr = pet_expr_set_arg( expr, 0, pet_length );
	return expr;
}

/* Construct a pet_expr that holds the sizes of an array of the given type.
 * The returned expression is a call expression with as arguments
 * the sizes in each dimension.  If we are unable to derive the size
 * in a given dimension, then the corresponding argument is set to infinity.
 * In fact, we initialize all arguments to infinity and then update
 * them if we are able to figure out the size.
 *
 * The result is stored in the type_size cache so that we can reuse
 * it if this method gets called on the same type again later on.
 */
__isl_give pet_expr *PetScan::get_array_size(const Type *type)
{
  cerr << __PRETTY_FUNCTION__ << endl;
	int depth;
	pet_expr *expr, *inf;

	if (type_size.find(type) != type_size.end())
		return pet_expr_copy(type_size[type]);

	depth = array_depth(type);
	inf = pet_expr_new_int(isl_val_infty(ctx));
	expr = pet_expr_new_call(ctx, "bounds", depth);
	for (int i = 0; i < depth; ++i)
		expr = pet_expr_set_arg(expr, i, pet_expr_copy(inf));
	pet_expr_free(inf);

	expr = set_upper_bounds(expr, type, 0);
	type_size[type] = pet_expr_copy(expr);

	return expr;
}

/* Construct a pet_expr that holds the sizes of a string literal.
 * The returned expression is a call expression with as arguments
 * the sizes in each dimension.   
 */
__isl_give pet_expr *PetScan::get_array_size(const StringLiteral* slit)
{
	int depth;
	pet_expr *expr, *inf;

	// cant be != 1
	depth = 1;

	inf = pet_expr_new_int(isl_val_infty(ctx));
	expr = pet_expr_new_call(ctx, "bounds", depth);
	for (int i = 0; i < depth; ++i)
		expr = pet_expr_set_arg(expr, i, pet_expr_copy(inf));
	pet_expr_free(inf);

	expr = set_upper_bounds(expr, slit);

	return expr;
}

/* Does "expr" represent the "integer" infinity?
 */
static int is_infty(__isl_keep pet_expr *expr)
{
	isl_val *v;
	int res;

	if (pet_expr_get_type(expr) != pet_expr_int)
		return 0;
	v = pet_expr_int_get_val(expr);
	res = isl_val_is_infty(v);
	isl_val_free(v);

	return res;
}

/* Figure out the dimensions of an array "array" based on its type
 * "type" and update "array" accordingly.
 *
 * We first construct a pet_expr that holds the sizes of the array
 * in each dimension.  The resulting expression may containing
 * infinity values for dimension where we are unable to derive
 * a size expression.
 *
 * The arguments of the size expression that have a value different from
 * infinity are then converted to an affine expression
 * within the context "pc" and incorporated into the size of "array".
 * If we are unable to convert a size expression to an affine expression or
 * if the size is not a (symbolic) constant,
 * then we leave the corresponding size of "array" untouched.
 */
struct pet_array *PetScan::set_upper_bounds(struct pet_array *array,
	const Type *type, __isl_keep pet_context *pc)
{
	int n;
	pet_expr *expr;

	if (!array)
		return NULL;

	expr = get_array_size(type);

	n = pet_expr_get_n_arg(expr);
	for (int i = 0; i < n; ++i) {
		pet_expr *arg;
		isl_pw_aff *size;

		arg = pet_expr_get_arg(expr, i);
		if (!is_infty(arg)) {
			int dim;

			size = pet_expr_extract_affine(arg, pc);
			dim = isl_pw_aff_dim(size, isl_dim_in);
			if (!size)
				array = pet_array_free(array);
			else if (isl_pw_aff_involves_nan(size) ||
			    isl_pw_aff_involves_dims(size, isl_dim_in, 0, dim))
				isl_pw_aff_free(size);
			else {
				size = isl_pw_aff_drop_dims(size,
							    isl_dim_in, 0, dim);
				array = update_size(array, i, size);
			}
		}
		pet_expr_free(arg);
	}
	pet_expr_free(expr);

	return array;
}

/* Does "decl" have a definition that we can keep track of in a pet_type?
 */
static bool has_printable_definition(RecordDecl *decl)
{
	if (!decl->getDeclName())
		return false;
	return decl->getLexicalDeclContext() == decl->getDeclContext();
}

/* Construct and return a pet_array corresponding to the variable "decl".
 * In particular, initialize array->extent to
 *
 *	{ name[i_1,...,i_d] : i_1,...,i_d >= 0 }
 *
 * and then call set_upper_bounds to set the upper bounds on the indices
 * based on the type of the variable.  The upper bounds are converted
 * to affine expressions within the context "pc".
 *
 * If the base type is that of a record with a top-level definition or
 * of a typedef and if "types" is not null, then the RecordDecl or
 * TypedefType corresponding to the type
 * is added to "types".
 *
 * If the base type is that of a record with no top-level definition,
 * then we replace it by "<subfield>".
 */
struct pet_array *PetScan::extract_array(isl_ctx *ctx, ValueDecl *decl,
	PetTypes *types, __isl_keep pet_context *pc)
{
  cerr << __PRETTY_FUNCTION__ << endl;
	struct pet_array *array;
	QualType qt = get_array_type(decl);
	const Type *type = qt.getTypePtr();
	int depth = array_depth(type);
	QualType base = pet_clang_base_type(qt);
	string name;
	isl_id *id;
	isl_space *dim;

	array = isl_calloc_type(ctx, struct pet_array);
	if (!array)
		return NULL;

	id = create_decl_id(ctx, decl);
	dim = isl_space_set_alloc(ctx, 0, depth);
	dim = isl_space_set_tuple_id(dim, isl_dim_set, id);

	array->extent = isl_set_nat_universe(dim);

	dim = isl_space_params_alloc(ctx, 0);
	array->context = isl_set_universe(dim);

	array = set_upper_bounds(array, type, pc);
	if (!array)
		return NULL;

	name = base.getAsString();

	if (types) {
		if (isa<TypedefType>(base)) {
			types->insert(cast<TypedefType>(base)->getDecl());
		} else if (base->isRecordType()) {
			RecordDecl *decl = pet_clang_record_decl(base);
			TypedefNameDecl *typedecl;
			typedecl = decl->getTypedefNameForAnonDecl();
			if (typedecl)
				types->insert(typedecl);
			else if (has_printable_definition(decl))
				types->insert(decl);
			else
				name = "<subfield>";
		}
	}

	array->element_type = strdup(name.c_str());
	array->element_is_record = base->isRecordType();
	array->element_size = size_in_bytes(decl->getASTContext(), base);

	return array;
}

/* Construct and return a pet_array corresponding to the sequence
 * of declarations "decls".
 * The upper bounds of the array are converted to affine expressions
 * within the context "pc".
 * If the sequence contains a single declaration, then it corresponds
 * to a simple array access.  Otherwise, it corresponds to a member access,
 * with the declaration for the substructure following that of the containing
 * structure in the sequence of declarations.
 * We start with the outermost substructure and then combine it with
 * information from the inner structures.
 *
 * Additionally, keep track of all required types in "types".
 */
struct pet_array *PetScan::extract_array(isl_ctx *ctx,
	vector<ValueDecl *> decls, PetTypes *types, __isl_keep pet_context *pc)
{
	struct pet_array *array;
	vector<ValueDecl *>::iterator it;

	it = decls.begin();

	array = extract_array(ctx, *it, types, pc);

	for (++it; it != decls.end(); ++it) {
		struct pet_array *parent;
		const char *base_name, *field_name;
		char *product_name;

		parent = array;
		array = extract_array(ctx, *it, types, pc);
		if (!array)
			return pet_array_free(parent);

		base_name = isl_set_get_tuple_name(parent->extent);
		field_name = isl_set_get_tuple_name(array->extent);
		product_name = pet_array_member_access_name(ctx,
							base_name, field_name);

		array->extent = isl_set_product(isl_set_copy(parent->extent),
						array->extent);
		if (product_name)
			array->extent = isl_set_set_tuple_name(array->extent,
								product_name);
		array->context = isl_set_intersect(array->context,
						isl_set_copy(parent->context));

		pet_array_free(parent);
		free(product_name);

		if (!array->extent || !array->context || !product_name)
			return pet_array_free(array);
	}

	return array;
}

/* For each of the fields of "decl" that is itself a record type
 * or a typedef, add a corresponding pet_type to "scop".
 */
struct pet_scop *PetScan::add_field_types(isl_ctx *ctx, struct pet_scop *scop,
	RecordDecl *decl, ASTContext &ast_context, PetTypes &types,
	std::set<TypeDecl *> &types_done)
{
	RecordDecl::field_iterator it;

	for (it = decl->field_begin(); it != decl->field_end(); ++it) {
		QualType type = it->getType();

		if (isa<TypedefType>(type)) {
			TypedefNameDecl *typedefdecl;

			typedefdecl = cast<TypedefType>(type)->getDecl();
			scop = add_type(ctx, scop, typedefdecl,
				ast_context, types, types_done);
		} else if (type->isRecordType()) {
			RecordDecl *record;

			record = pet_clang_record_decl(type);
			scop = add_type(ctx, scop, record,
				ast_context, types, types_done);
		}
	}

	return scop;
}

/* Add a pet_type corresponding to "decl" to "scop", provided
 * it is a member of types.records and it has not been added before
 * (i.e., it is not a member of "types_done").
 *
 * Since we want the user to be able to print the types
 * in the order in which they appear in the scop, we need to
 * make sure that types of fields in a structure appear before
 * that structure.  We therefore call ourselves recursively
 * through add_field_types on the types of all record subfields.
 */
struct pet_scop *PetScan::add_type(isl_ctx *ctx, struct pet_scop *scop,
	RecordDecl *decl, ASTContext &ast_context, PetTypes &types,
	std::set<TypeDecl *> &types_done)
{
	string s;
	llvm::raw_string_ostream S(s);

	if (types.records.find(decl) == types.records.end())
		return scop;
	if (types_done.find(decl) != types_done.end())
		return scop;

	add_field_types(ctx, scop, decl, ast_context, types, types_done);

	if (strlen(decl->getName().str().c_str()) == 0)
		return scop;

	decl->print(S, PrintingPolicy(ast_context.getLangOpts()));
	S.str();

	scop->types[scop->n_type] = pet_type_alloc(ctx,
				    decl->getName().str().c_str(), s.c_str());
	if (!scop->types[scop->n_type])
		return pet_scop_free(scop);

	types_done.insert(decl);

	scop->n_type++;

	return scop;
}

/* Add a pet_type corresponding to "decl" to "scop", provided
 * it is a member of types.typedefs and it has not been added before
 * (i.e., it is not a member of "types_done").
 *
 * If the underlying type is a structure, then we print the typedef
 * ourselves since clang does not print the definition of the structure
 * in the typedef.  We also make sure in this case that the types of
 * the fields in the structure are added first.
 */
struct pet_scop *PetScan::add_type(isl_ctx *ctx, struct pet_scop *scop,
	TypedefNameDecl *decl, ASTContext &ast_context, PetTypes &types,
	std::set<TypeDecl *> &types_done)
{
	string s;
	llvm::raw_string_ostream S(s);
	QualType qt = decl->getUnderlyingType();

	if (types.typedefs.find(decl) == types.typedefs.end())
		return scop;
	if (types_done.find(decl) != types_done.end())
		return scop;

	if (qt->isRecordType()) {
		RecordDecl *rec = pet_clang_record_decl(qt);

		add_field_types(ctx, scop, rec, ast_context, types, types_done);
		S << "typedef ";
		rec->print(S, PrintingPolicy(ast_context.getLangOpts()));
		S << " ";
		S << decl->getName();
	} else {
		decl->print(S, PrintingPolicy(ast_context.getLangOpts()));
	}
	S.str();

	scop->types[scop->n_type] = pet_type_alloc(ctx,
				    decl->getName().str().c_str(), s.c_str());
	if (!scop->types[scop->n_type])
		return pet_scop_free(scop);

	types_done.insert(decl);

	scop->n_type++;

	return scop;
}

/* Construct a list of pet_arrays, one for each array (or scalar)
 * accessed inside "scop", add this list to "scop" and return the result.
 * The upper bounds of the arrays are converted to affine expressions
 * within the context "pc".
 *
 * The context of "scop" is updated with the intersection of
 * the contexts of all arrays, i.e., constraints on the parameters
 * that ensure that the arrays have a valid (non-negative) size.
 *
 * If any of the extracted arrays refers to a member access or
 * has a typedef'd type as base type,
 * then also add the required types to "scop".
 */
struct pet_scop *PetScan::scan_arrays(struct pet_scop *scop,
	__isl_keep pet_context *pc)
{
	std::cerr << __FILE__ << " " << __LINE__ << std::endl;
	int i, n;
	array_desc_set arrays;
	array_desc_set::iterator it;
	PetTypes types;
	std::set<TypeDecl *> types_done;
	std::set<clang::RecordDecl *, less_name>::iterator records_it;
	std::set<clang::TypedefNameDecl *, less_name>::iterator typedefs_it;
	int n_array;
	struct pet_array **scop_arrays;

	if (!scop)
		return NULL;

	std::cerr << __FILE__ << " " << __LINE__ << std::endl;
	pet_scop_collect_arrays(scop, arrays);
	std::cerr << __FILE__ << " " << __LINE__ << std::endl;

	if (arrays.size() == 0)
		return scop;

	n_array = scop->n_array;

	scop_arrays = isl_realloc_array(ctx, scop->arrays, struct pet_array *,
					n_array + arrays.size());
	if (!scop_arrays)
		goto error;
	scop->arrays = scop_arrays;

	for (it = arrays.begin(), i = 0; it != arrays.end(); ++it, ++i) {
		std::cerr << __FILE__ << " " << __LINE__ << std::endl;
		struct pet_array *array;
		array = extract_array(ctx, *it, &types, pc);
		scop->arrays[n_array + i] = array;
		if (!scop->arrays[n_array + i])
			goto error;
		scop->n_array++;
		scop->context = isl_set_intersect(scop->context,
						isl_set_copy(array->context));
		if (!scop->context)
			goto error;
	}

	n = types.records.size() + types.typedefs.size();
	if (n == 0)
		return scop;

	scop->types = isl_alloc_array(ctx, struct pet_type *, n);
	if (!scop->types)
		goto error;

	for (records_it = types.records.begin();
	     records_it != types.records.end(); ++records_it)
		scop = add_type(ctx, scop, *records_it, ast_context, types, types_done);

	for (typedefs_it = types.typedefs.begin();
	     typedefs_it != types.typedefs.end(); ++typedefs_it)
		scop = add_type(ctx, scop, *typedefs_it, ast_context, types, types_done);

	return scop;
error:
	pet_scop_free(scop);
	return NULL;
}

/* Bound all parameters in scop->context to the possible values
 * of the corresponding C variable.
 */
struct pet_scop *PetScan::add_parameter_bounds(struct pet_scop *scop)
{
	int n;

	if (!scop)
		return NULL;

	n = isl_set_dim(scop->context, isl_dim_param);
	for (int i = 0; i < n; ++i) {
		isl_id *id;
		ValueDecl *decl;

		id = isl_set_get_dim_id(scop->context, isl_dim_param, i);
		if (pet_nested_in_id(id)) {
			isl_id_free(id);
			isl_die(isl_set_get_ctx(scop->context),
				isl_error_internal,
				"unresolved nested parameter", goto error);
		}
		decl = (ValueDecl *) isl_id_get_user(id);
		isl_id_free(id);

		scop->context = set_parameter_bounds(scop->context, i, decl);

		if (!scop->context)
			goto error;
	}

	return scop;
error:
	pet_scop_free(scop);
	return NULL;
}

/* Construct a pet_scop from the given function.
 *
 * If the scop was delimited by scop and endscop pragmas, then we override
 * the file offsets by those derived from the pragmas.
 */
struct pet_scop *PetScan::scan(FunctionDecl *fd)
{
	pet_scop *scop;
	Stmt *stmt;

	stmt = fd->getBody();

	if (options->autodetect) {
		set_current_stmt(stmt);
		scop = extract_scop(extract(stmt, true));
	} else {
		current_line = loc.start_line;
		scop = scan(stmt);
		scop = pet_scop_update_start_end(scop, loc.start, loc.end);
	}
	scop = add_parameter_bounds(scop);
	scop = pet_scop_gist(scop, value_bounds);

	return scop;
}

/* Update this->last_line and this->current_line based on the fact
 * that we are about to consider "stmt".
 */
void PetScan::set_current_stmt(Stmt *stmt)
{
	SourceLocation loc = stmt->getLocStart();
	SourceManager &SM = ast_context.getSourceManager();

	last_line = current_line;
	current_line = SM.getExpansionLineNumber(loc);
}

/* Is the current statement marked by an independent pragma?
 * That is, is there an independent pragma on a line between
 * the line of the current statement and the line of the previous statement.
 * The search is not implemented very efficiently.  We currently
 * assume that there are only a few independent pragmas, if any.
 */
bool PetScan::is_current_stmt_marked_independent()
{
	for (int i = 0; i < independent.size(); ++i) {
		unsigned line = independent[i].line;

		if (last_line < line && line < current_line)
			return true;
	}

	return false;
}
