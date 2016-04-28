
#include "isl_type_information.h"

#include <map>

using namespace std;

std::map<void*, IslIdTypeInformation> isl_id_type_map;

void* register_user_data_type( void* p, int type ){
  isl_id_type_map[p] = (IslIdTypeInformation)type;
  return p;
} 

int get_isl_id_user_data_type( void* p ){
  auto find = isl_id_type_map.find( p );
  if ( find == isl_id_type_map.end() ) return (int)ITI_Unknown;
  return (int)find->second;
}
