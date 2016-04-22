CMAKE_MINIMUM_REQUIRED(VERSION 2.6)
PROJECT(libpet)

SET( CMAKE_BUILD_TYPE RELEASE )




enable_testing()

FILE(GLOB inFiles  "${CMAKE_SOURCE_DIR}/tests/*.c")

FOREACH( file_name ${inFiles} ) 
  add_test( NAME ${file_name} COMMAND test_file.sh ${file_name} )
ENDFOREACH()


FILE(GLOB inFiles  "${CMAKE_SOURCE_DIR}/tests/autodetect/*.c")

FOREACH( file_name ${inFiles} ) 
  add_test( NAME ${file_name} COMMAND test_file.sh ${file_name} --autodetect )
ENDFOREACH()

FILE(GLOB inFiles  "${CMAKE_SOURCE_DIR}/tests/encapsulate/*.c")

FOREACH( file_name ${inFiles} ) 
  add_test( NAME ${file_name} COMMAND test_file.sh ${file_name} --encapsulate-dynamic-control )
ENDFOREACH()
