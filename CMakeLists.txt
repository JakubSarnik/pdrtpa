cmake_minimum_required(VERSION 3.25)
project(pdrtpa)

include(ExternalProject)

set(CMAKE_CXX_STANDARD 23)

add_library(aiger STATIC dep/aiger/aiger.c)
set(AIGER_HEADER_DIR "${CMAKE_SOURCE_DIR}/dep/aiger")

# CaDiCaL is not a CMake project and is built according to dep/cadical/BUILD.md
# Note that with the following settings, it is always built optimized and without
# debug symbols, even for a debug build of this project.

ExternalProject_Add(cadical_build
        SOURCE_DIR "${CMAKE_SOURCE_DIR}/dep/cadical"
        CONFIGURE_COMMAND "${CMAKE_SOURCE_DIR}/dep/cadical/configure"
        BUILD_COMMAND "make"
        INSTALL_COMMAND ""
        TEST_COMMAND ""
        UPDATE_COMMAND ""
        PATCH_COMMAND ""
        BUILD_IN_SOURCE 1 # We need this because the configure script contains relative paths
)

set(CADICAL_HEADER_DIR "${CMAKE_SOURCE_DIR}/dep/cadical/src")
set(CADICAL_BINARY_DIR "${CMAKE_SOURCE_DIR}/dep/cadical/build")

add_library(cadical STATIC IMPORTED)
set_target_properties(cadical PROPERTIES IMPORTED_LOCATION "${CADICAL_BINARY_DIR}/libcadical.a")
add_dependencies(cadical cadical_build)

add_library(pdrtpa-lib STATIC
        src/logic.hpp
        src/logger.hpp
        src/aiger_builder.hpp
        src/aiger_builder.cpp
        src/transition_system.hpp
        src/solver.hpp
        src/verifier.cpp
        src/verifier.hpp
        src/aiger.hpp
        src/simplifier.cpp
        src/simplifier.hpp
)

target_link_libraries(pdrtpa-lib PUBLIC aiger)
target_link_libraries(pdrtpa-lib PUBLIC cadical)

target_include_directories(pdrtpa-lib PUBLIC "${CMAKE_SOURCE_DIR}/src")
target_include_directories(pdrtpa-lib PUBLIC "${AIGER_HEADER_DIR}")
target_include_directories(pdrtpa-lib PUBLIC "${CADICAL_HEADER_DIR}")

add_executable(pdrtpa src/main.cpp)
target_link_libraries(pdrtpa PUBLIC pdrtpa-lib)

add_subdirectory(test)
