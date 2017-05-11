#include <map>

#include <clang/Basic/SourceManager.h>
#include <clang/AST/Decl.h>
#include <clang/AST/Stmt.h>
#include <clang/Lex/Preprocessor.h>
#include <clang/AST/StmtIterator.h>

#include <isl/ctx.h>
#include <isl/map.h>
#include <isl/val.h>

#include "context.h"
#include "loc.h"
#include "scop.h"
#include "summary.h"
#include "tree.h"

namespace clang{
	typedef clang::Stmt::child_range StmtRange;
}

/* The location of the scop, as delimited by scop and endscop
 * pragmas by the user.
 * "start_line" is the line number of the start position.
 */
struct ScopLoc {
	ScopLoc() : end(0) {}

	unsigned start_line;
	unsigned start;
	unsigned end;
};

/* The information extracted from a pragma pencil independent.
 * We currently only keep track of the line number where
 * the pragma appears.
 */
struct Independent {
	Independent(unsigned line) : line(line) {}

	unsigned line;
};

/* Compare two TypeDecl pointers based on their names.
 */
struct less_name {
	bool operator()(const clang::TypeDecl *x,
			const clang::TypeDecl *y) {
		return x->getNameAsString().compare(y->getNameAsString()) < 0;
	}
};

/* The PetTypes structure collects a set of RecordDecl and
 * TypedefNameDecl pointers.
 * The pointers are sorted using a fixed order.  The actual order
 * is not important, only that it is consistent across platforms.
 */
struct PetTypes {
	std::set<clang::RecordDecl *, less_name> records;
	std::set<clang::TypedefNameDecl *, less_name> typedefs;

	void insert(clang::RecordDecl *decl) {
		records.insert(decl);
	}
	void insert(clang::TypedefNameDecl *decl) {
		typedefs.insert(decl);
	}
};

struct PetScan {
	clang::ASTContext &ast_context;
	/* If autodetect is false, then loc contains the location
	 * of the scop to be extracted.
	 */
	ScopLoc &loc;
	isl_ctx *ctx;
	pet_options *options;
	/* Set if the pet_scop returned by an extract method only
	 * represents part of the input tree.
	 */
	bool partial;

	/* Set if increment other then by one is not allowed */
	bool increment_by_one = true;

	/* A cache of size expressions for array types as computed
	 * by PetScan::get_array_size.
	 */
	std::map<const clang::Type *, pet_expr *> type_size;

	/* A cache of funtion summaries for function declarations
	 * as extracted by PetScan::get_summary.
	 */
	std::map<clang::FunctionDecl *, pet_function_summary *> summary_cache;

	std::map<clang::VarDecl*, clang::VarDecl*> iterator_to_index_map;

	/* A union of mappings of the form
	 *	{ identifier[] -> [i] : lower_bound <= i <= upper_bound }
	 */
	isl_union_map *value_bounds;

	/* The line number of the previously considered Stmt. */
	unsigned last_line;
	/* The line number of the Stmt currently being considered. */
	unsigned current_line;
	/* Information about the independent pragmas in the source code. */
	std::vector<Independent> &independent;

	unsigned int call_ctr = 0;
	std::unique_ptr<std::map<std::string, std::string>> name_to_text;

	clang::DiagnosticsEngine* diagnosticsEngine = nullptr;

	PetScan(clang::ASTContext &ast_context, ScopLoc &loc,
		pet_options *options, __isl_take isl_union_map *value_bounds,
		std::vector<Independent> &independent) :
		ctx(isl_union_map_get_ctx(value_bounds)), 
		ast_context(ast_context), loc(loc),
		options(options), value_bounds(value_bounds),
		partial(false), last_line(0), current_line(0),
		independent(independent) { 
	    
	  name_to_text.reset( new std::map<std::string, std::string>() );

	}

	~PetScan();

	struct pet_scop *scan(clang::FunctionDecl *fd);

	static __isl_give isl_val *extract_int(isl_ctx *ctx,
		clang::IntegerLiteral *expr);
	__isl_give pet_expr *get_array_size(const clang::Type *type);
	__isl_give pet_expr *get_array_size(const clang::StringLiteral* slit);
	struct pet_array *extract_array(isl_ctx *ctx, clang::ValueDecl *decl,
		PetTypes *types, __isl_keep pet_context *pc);
private:
	void set_current_stmt(clang::Stmt *stmt);
	bool is_current_stmt_marked_independent();
	bool isIncrementByOne( pet_expr* expr);

	clang::DiagnosticsEngine& getDiagnostics();

	struct pet_scop *scan(clang::Stmt *stmt);

	struct pet_scop *scan_arrays(struct pet_scop *scop,
		__isl_keep pet_context *pc);
	struct pet_array *extract_array(isl_ctx *ctx,
		std::vector<clang::ValueDecl *> decls,
		PetTypes *types, __isl_keep pet_context *pc);
	__isl_give pet_expr *set_upper_bounds(__isl_take pet_expr *expr,
		const clang::Type *type, int pos);
	__isl_give pet_expr *set_upper_bounds(__isl_take pet_expr *expr, const clang::StringLiteral* slit);
	struct pet_array *set_upper_bounds(struct pet_array *array,
		const clang::Type *type, __isl_keep pet_context *pc);

	__isl_give pet_tree *insert_initial_declarations(
		__isl_take pet_tree *tree, int n_decl,
		clang::StmtRange stmt_range);
	__isl_give pet_tree *extract(clang::Stmt *stmt,
		bool skip_declarations = false);
	__isl_give pet_tree *extract(clang::StmtRange stmt_range, bool block,
		bool skip_declarations);
	__isl_give pet_tree *extract(clang::IfStmt *stmt);
	__isl_give pet_tree *extract(clang::WhileStmt *stmt);
	__isl_give pet_tree *extract(clang::CompoundStmt *stmt,
		bool skip_declarations = false);
	__isl_give pet_tree *extract(clang::LabelStmt *stmt);
	__isl_give pet_tree *extract(clang::Decl *decl);
	__isl_give pet_tree *extract(clang::DeclStmt *expr);
	__isl_give pet_tree *extract(clang::ReturnStmt *expr);

	__isl_give pet_loc *construct_pet_loc(clang::SourceRange range,
		bool skip_semi);
	__isl_give pet_tree *extract(__isl_take pet_expr *expr,
		clang::SourceRange range, bool skip_semi);
	__isl_give pet_tree *update_loc(__isl_take pet_tree *tree,
		clang::Stmt *stmt);

	struct pet_scop *extract_scop(__isl_take pet_tree *tree);

	clang::BinaryOperator *initialization_assignment(clang::Stmt *init);
	clang::Decl *initialization_declaration(clang::Stmt *init);
	clang::ValueDecl *extract_induction_variable(clang::BinaryOperator *stmt);
	clang::VarDecl *extract_induction_variable(clang::Stmt *init,
				clang::Decl *stmt);
	__isl_give pet_expr *extract_unary_increment(clang::UnaryOperator *op,
				clang::ValueDecl *iv);
	__isl_give pet_expr *extract_unary_increment( 
		clang::CXXOperatorCallExpr* expr,
		clang::ValueDecl* iv
	);
	__isl_give pet_expr *extract_binary_increment(
				clang::BinaryOperator *op,
				clang::ValueDecl *iv);
	__isl_give pet_expr *extract_compound_increment(
				clang::CompoundAssignOperator *op,
				clang::ValueDecl *iv);
	__isl_give pet_expr *extract_increment(clang::ForStmt *stmt,
				clang::ValueDecl *iv);
	__isl_give pet_tree *extract_for(clang::ForStmt *stmt);
	__isl_give pet_tree *extract_range_for(clang::CXXForRangeStmt *stmt);

	__isl_give pet_expr *extract_assume(clang::Expr *expr);
	__isl_give pet_function_summary *get_summary(clang::FunctionDecl *fd);
	__isl_give pet_expr *set_summary(__isl_take pet_expr *expr,
		clang::FunctionDecl *fd);
	__isl_give pet_expr *extract_argument(clang::FunctionDecl *fd, int pos,
		clang::Expr *expr, bool detect_writes);
	__isl_give pet_expr *extract_expr(const llvm::APInt &val);
	__isl_give pet_expr *extract_expr(clang::Expr *expr);
	__isl_give pet_expr *extract_expr(clang::UnaryOperator *expr);
	__isl_give pet_expr *extract_expr(clang::BinaryOperator *expr);
	__isl_give pet_expr *extract_expr(clang::ImplicitCastExpr *expr);
	__isl_give pet_expr *extract_expr(clang::IntegerLiteral *expr);
	__isl_give pet_expr *extract_expr(clang::CXXBoolLiteralExpr *expr);
	__isl_give pet_expr *extract_expr(clang::EnumConstantDecl *expr);
	__isl_give pet_expr *extract_expr(clang::FloatingLiteral *expr);
	__isl_give pet_expr *extract_expr(clang::ParenExpr *expr);
	__isl_give pet_expr *extract_expr(clang::ConditionalOperator *expr);
	__isl_give pet_expr *extract_expr(clang::CallExpr *expr);
	__isl_give pet_expr *extract_expr(clang::CStyleCastExpr *expr);
	__isl_give pet_expr *extract_expr(clang::SubstNonTypeTemplateParmExpr *expr);
	__isl_give pet_expr *extract_cxx_expr(clang::Expr *expr);
	__isl_give pet_expr *extract_cxx_binary_operator(clang::CXXOperatorCallExpr *expr, clang::OverloadedOperatorKind ook);
	__isl_give pet_expr *extract_cxx_unary_operator(clang::CXXOperatorCallExpr *expr, clang::OverloadedOperatorKind ook );
        __isl_give pet_expr *extract_expr_from_stream(clang::CXXOperatorCallExpr *op);

	__isl_give pet_expr *extract_expr(clang::MaterializeTemporaryExpr *expr);
	__isl_give pet_expr *extract_expr(clang::CXXMemberCallExpr *expr);
	__isl_give pet_expr *extract_expr(clang::ExprWithCleanups *expr);

	__isl_give pet_expr *extract_access_expr(clang::QualType qt,
		__isl_take pet_expr *index);
	__isl_give pet_expr *extract_access_expr(clang::Expr *expr);
	__isl_give pet_expr *extract_access_expr(clang::ValueDecl *decl);

	__isl_give pet_expr *extract_index_expr(
		clang::ArraySubscriptExpr *expr);
	__isl_give pet_expr *extract_index_expr(clang::Expr *expr);
	__isl_give pet_expr *extract_index_expr(clang::ImplicitCastExpr *expr);
	__isl_give pet_expr *extract_index_expr(clang::DeclRefExpr *expr);
	__isl_give pet_expr *extract_index_expr(clang::ValueDecl *decl);
	__isl_give pet_expr *extract_index_expr(clang::MemberExpr *expr);
	__isl_give pet_expr *extract_index_expr(clang::CallExpr *expr);
	__isl_give pet_expr *extract_index_expr(clang::CXXMemberCallExpr *expr);
	__isl_give pet_expr *extract_index_expr(clang::CXXConstructExpr *expr);
	__isl_give pet_expr *extract_index_expr(clang::MaterializeTemporaryExpr *expr);
	__isl_give pet_expr *extract_index_expr(clang::StringLiteral *expr);
	__isl_give pet_expr *extract_index_expr(clang::CXXOperatorCallExpr *expr);
	__isl_give pet_expr *extract_index_expr_unary(clang::CXXOperatorCallExpr *expr);

	__isl_give isl_val *extract_int(clang::Expr *expr);
	__isl_give isl_val *extract_int(clang::ParenExpr *expr);

	clang::FunctionDecl *find_decl_from_name(clang::CallExpr *call,
		std::string name);
	clang::FunctionDecl *get_summary_function(clang::CallExpr *call);

	pet_expr* build_iterator_unequal_comparison( clang::Expr* lhs, clang::Expr* rhs );
	pet_expr* iterator_init_transformation( clang::Expr* rhs );
	clang::VarDecl* get_or_create_iterator_replacement( clang::VarDecl* iterator_decl );
	std::string createCallPlaceholder( std::string call_text );
        void check_stream_reference( clang::DeclRefExpr* expr );
        std::string get_container_name_from_iterator( clang::Expr* expr);
        clang::VarDecl* isIterator( clang::Expr* expr);
        clang::VarDecl* extract_container( clang::Expr* e );
        clang::DeclRefExpr* build_base_expression_by_initializer( clang::Expr* e );
        clang::DeclRefExpr* build_index_expression_by_decl( clang::Expr* e );
        bool isStdContainerIteratorCreator( std::string name );
        bool isIteratorType( const clang::Type* type_ptr );
        bool isIteratorType( clang::QualType qt );
        int get_type_size(clang::QualType qt, clang::ASTContext &ast_context);
        int get_type_size(clang::ValueDecl *decl);
        struct pet_scop *add_parameter_bounds(struct pet_scop *scop);

        struct pet_scop *add_type(isl_ctx *ctx, struct pet_scop *scop,
            clang::TypedefNameDecl *decl, clang::ASTContext &ast_context, PetTypes &types,
            std::set<clang::TypeDecl *> &types_done);

        struct pet_scop *add_type(isl_ctx *ctx, struct pet_scop *scop,
            clang::RecordDecl *decl, clang::ASTContext &ast_context, PetTypes &types,
            std::set<clang::TypeDecl *> &types_done);

        struct pet_scop *add_field_types(isl_ctx *ctx, struct pet_scop *scop,
            clang::RecordDecl *decl, clang::ASTContext &ast_context, PetTypes &types,
            std::set<clang::TypeDecl *> &types_done);


        __isl_give isl_set *set_parameter_bounds(__isl_take isl_set *set,
          unsigned pos, clang::ValueDecl *decl);


        clang::VarDecl* extract_member_call( clang::Expr* e );
        clang::VarDecl* extract_container_from_instance( clang::Expr* instance, clang::CXXMemberCallExpr* member_call );

	void report(clang::Stmt *stmt, unsigned id, std::string debug_information = "" );
	void unsupported(clang::Stmt *stmt);
	void unsupported_with_extra_string(clang::Stmt *stmt, std::string extra );
	void warning_assume_with_extra_string(clang::Stmt *stmt, std::string extra );
	void note_understood_with_extra_string(clang::Stmt *stmt, std::string extra);
	//void report_unsupported_statement_type(clang::Stmt *stmt);
	void report_unsupported_statement_type_with_extra_string(clang::Stmt *stmt, std::string extra);
	void report_prototype_required(clang::Stmt *stmt);
	void report_missing_increment(clang::Stmt *stmt);
	void report_missing_summary_function(clang::Stmt *stmt);
	void report_missing_summary_function_body(clang::Stmt *stmt);

	bool treat_calls_like_access = false;
	bool isPureOrConst( clang::FunctionDecl* fdecl );
	void checkPureOrConst( clang::CallExpr* call );

};
