
# Try to find the pet library

# PET_FOUND       - System has isl lib
# PET_INCLUDE_DIR - The isl include directory
# PET_LIBRARY     - Library needed to use isl


if (PET_INCLUDE_DIR AND PET_LIBRARY)
	# Already in cache, be silent
	set(PET_FIND_QUIETLY TRUE)
endif()

find_path(PET_INCLUDE_DIR NAMES include/pet_cxx.h)
find_library(PET_LIBRARY NAMES lib/libpet_cxx.a )

get_filename_component( PET_LIBRARY_DIR ${PET_LIBRARY} DIRECTORY )

set ( PET_ISL_INCLUDE_DIR ${PET_INCLUDE_DIR} )
set ( PET_ISL_LIBRARY "${PET_LIBRARY_DIR}/libisl.so.15" )

if (PET_LIBRARY AND PET_INCLUDE_DIR)
	message(STATUS "Library pet found =) ${PET_LIBRARY}")
	message(STATUS "Library pet-isl found =) ${PET_ISL_LIBRARY}")
	message(STATUS "Include pet-isl found =) ${PET_ISL_INCLUDE_DIR}")
else()
	message(STATUS "Library pet not found =(")
endif()

include(FindPackageHandleStandardArgs)
FIND_PACKAGE_HANDLE_STANDARD_ARGS(PET DEFAULT_MSG PET_INCLUDE_DIR PET_LIBRARY)

mark_as_advanced(PET_INCLUDE_DIR PET_LIBRARY PET_INCLUDE_DIR PET_ISL_LIBRARY )
