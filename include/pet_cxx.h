
#pragma once

#include <clang/AST/ASTContext.h>
#include <clang/Lex/Preprocessor.h>
#include <clang/Sema/Sema.h>
#include <isl/ctx.h>

struct pet_scop;


struct PetASTConsumer;
struct ScopLocList;
struct pet_options;

class Pet {

  public:

    Pet( 
	    clang::DiagnosticsEngine& Diags,
	    clang::ASTContext* clang_ctx
    );

    ~Pet(); 

    void initialize_consumer( clang::ASTContext* clang_ctx );
    void pet_scop_extract_from_clang_ast( 
      clang::ASTContext* context,
      clang::ForStmt* stmt,
      clang::FunctionDecl* fd,
      std::unique_ptr<std::map<std::string,std::string>>& call_texts,
      pet_scop** _scop
    );

  private:
    isl_ctx* ctx = nullptr;
    clang::DiagnosticsEngine* diags;
    PetASTConsumer* consumer = nullptr;
    bool consumer_initialized = false;
    pet_scop* scop = nullptr;
    ScopLocList* scops;

};
