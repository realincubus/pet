
#pragma once

#include <clang/AST/ASTContext.h>
#include <clang/Lex/Preprocessor.h>
#include <isl/ctx.h>

pet_scop* pet_scop_extract_from_clang_ast( isl_ctx* ctx,
				      clang::Preprocessor& PP,
				      clang::ASTContext& clang_ctx,
				      clang::DiagnosticsEngine& Diags,
				      pet_options* options,
				      clang::DeclGroupRef dg
				    ); 
				       

struct pet_options {
	/* If autodetect is false, a scop delimited by pragmas is extracted,
	 * otherwise we take any scop that we can find.
	 */
	int	autodetect;
	int	detect_conditional_assignment;
	/* If encapsulate_dynamic_control is set, then any dynamic control
	 * in the input program will be encapsulated in macro statements.
	 * This means in particular that no statements with arguments
	 * will be created.
	 */
	int	encapsulate_dynamic_control;
	/* Support pencil builtins and pragmas */
	int	pencil;
	int	n_path;
	const char **paths;
	int	n_define;
	const char **defines;

	unsigned signed_overflow;
};


