CMAKE_MINIMUM_REQUIRED(VERSION 2.6)

SET( CMAKE_BUILD_TYPE RELEASE )
SET( TEST_COMMAND ${CMAKE_SOURCE_DIR}/test_file.sh )
SET( PET_COMMAND ${CMAKE_SOURCE_DIR}/pet )
SET( PET_SCOP_CMP_COMMAND ${CMAKE_SOURCE_DIR}/pet_scop_cmp )

enable_testing()

FILE(GLOB inFiles  "${CMAKE_SOURCE_DIR}/tests/*.c")

FOREACH( file_name ${inFiles} ) 
  add_test( NAME ${file_name} COMMAND  ${TEST_COMMAND} ${PET_COMMAND} ${PET_SCOP_CMP_COMMAND}  ${file_name} )
ENDFOREACH()


FILE(GLOB inFiles  "${CMAKE_SOURCE_DIR}/tests/autodetect/*.c")

FOREACH( file_name ${inFiles} ) 
  add_test( NAME ${file_name} COMMAND  ${TEST_COMMAND} ${PET_COMMAND} ${PET_SCOP_CMP_COMMAND} ${file_name} --autodetect )
ENDFOREACH()

FILE(GLOB inFiles  "${CMAKE_SOURCE_DIR}/tests/encapsulate/*.c")

FOREACH( file_name ${inFiles} ) 
  add_test( NAME ${file_name} COMMAND  ${TEST_COMMAND} ${PET_COMMAND} ${PET_SCOP_CMP_COMMAND}  ${file_name} --encapsulate-dynamic-control )
ENDFOREACH()
