CMAKE_MINIMUM_REQUIRED(VERSION 2.6)

configure_file( isl-download/CMakeLists.txt.in isl-download/CMakeLists.txt)
execute_process( COMMAND ${CMAKE_COMMAND} -G ${CMAKE_GENERATOR} . WORKING_DIRECTORY isl-download)
execute_process( COMMAND ${CMAKE_COMMAND} --build . WORKING_DIRECTORY isl-download )

add_library( pet isl_type_information.cc
aff.h
aff.c
array.h
array.c
clang.h
clang.cc
context.h
context.c
expr.h
expr.c
expr_access_type.h
expr_arg.h
expr_arg.c
filter.h
filter.c
loc.h
loc.c
nest.h
nest.c
options.h
options.c
print.c
print.h
tree.h
tree.c
tree2scop.h
tree2scop.c
scan.h
scan.cc
scop.h
scop.c
scop_plus.h
scop_plus.cc
skip.h
skip.c
state.h
summary.h
summary.c
value_bounds.h
value_bounds.c
version.h
version.cc
initialize_pet.c
pet.cc )

target_include_directories( pet PRIVATE ${CMAKE_BINARY_DIR}/isl-src/include )
target_include_directories( pet PRIVATE /usr/lib/llvm-3.8/include )
target_include_directories( pet PRIVATE ${CMAKE_SOURCE_DIR}/include )
set_property( TARGET pet PROPERTY CXX_STANDARD 11)
target_link_libraries( pet
        clangParse
        clangSema
        clangFrontend
        clangDriver
        clangAnalysis
        clangAST
        clangLex clangBasic
        clangSerialization
        ${CMAKE_BINARY_DIR}/isl-src/.libs/libisl.a
        dl z cursesw
        )

#SET( CMAKE_BUILD_TYPE RELEASE )
SET( TEST_COMMAND ${CMAKE_SOURCE_DIR}/test_file.sh )
SET( PET_COMMAND ${CMAKE_SOURCE_DIR}/pet )
SET( PET_SCOP_CMP_COMMAND ${CMAKE_SOURCE_DIR}/pet_scop_cmp )

enable_testing()

# c tests 
FILE(GLOB inFiles  "${CMAKE_SOURCE_DIR}/tests/*.c")

FOREACH( file_name ${inFiles} ) 
  add_test( NAME ${file_name} COMMAND  ${TEST_COMMAND} ${PET_COMMAND} ${PET_SCOP_CMP_COMMAND}  ${file_name} )
ENDFOREACH()

# c plus plus tests

FILE(GLOB inFiles  "${CMAKE_SOURCE_DIR}/tests/*.cc")

FOREACH( file_name ${inFiles} ) 
  add_test( NAME ${file_name} COMMAND  ${TEST_COMMAND} ${PET_COMMAND} ${PET_SCOP_CMP_COMMAND}  ${file_name} )
ENDFOREACH()

# autodetect tests (c)

FILE(GLOB inFiles  "${CMAKE_SOURCE_DIR}/tests/autodetect/*.c")

FOREACH( file_name ${inFiles} ) 
  add_test( NAME ${file_name} COMMAND  ${TEST_COMMAND} ${PET_COMMAND} ${PET_SCOP_CMP_COMMAND} ${file_name} --autodetect )
ENDFOREACH()

# encapsulate tests (c)

FILE(GLOB inFiles  "${CMAKE_SOURCE_DIR}/tests/encapsulate/*.c")

FOREACH( file_name ${inFiles} ) 
  add_test( NAME ${file_name} COMMAND  ${TEST_COMMAND} ${PET_COMMAND} ${PET_SCOP_CMP_COMMAND}  ${file_name} --encapsulate-dynamic-control )
ENDFOREACH()
