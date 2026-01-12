#pragma once

#include "aiger.hpp"
#include "catch2/catch_test_macros.hpp"

inline aiger_ptr read_aiger( const char* str )
{
    auto aig = make_aiger();
    const auto* const err = aiger_read_from_string( aig.get(), str );

    REQUIRE( err == nullptr );

    return aig;
}