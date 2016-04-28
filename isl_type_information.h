
#pragma once

#if defined(__cplusplus)
extern "C" {
#endif


#if 0
struct Wrapper {
    void* content;
    int dummy;
};

inline void* wrap_impl( void* nd, int line ){
  if ( nd == NULL ) return NULL;
  struct Wrapper* w = (struct Wrapper*)malloc( sizeof(struct Wrapper) );
  w->content = nd;
  w->dummy = line;
  fprintf(stderr,"wrapped %d in %d line %d\n", nd, w, line);
  return w;
}

#define wrap(x) wrap_impl( (x), __LINE__ ) 

inline void* unwrap_impl( void* user_data, const char* pos, int line ){
  if ( user_data == NULL ) return NULL;
  struct Wrapper* w = (struct Wrapper*)user_data;
  fprintf(stderr,"%s %d: unwrapped %d to %d from line %d\n",pos, line, user_data, w->content, w->dummy );
  void* ret = w->content;
  return ret;
}

#define unwrap(x) unwrap_impl( (x), __FILE__, __LINE__ ) 
#endif

enum IslIdTypeInformation {
    ITI_Unknown,
    ITI_NamedDecl,
    ITI_StringLiteral,
    ITI_ListEnd
};

void* register_user_data_type( void* udo, int type );
int get_isl_id_user_data_type( void* p );

#if defined(__cplusplus)
}
#endif


