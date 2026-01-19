#include "common.hpp"
#include "logic.hpp"
#include "transition_system.hpp"
#include "aiger_builder.hpp"
#include "verifier.hpp"
#include <algorithm>

namespace
{

transition_system system_from_aiger( variable_store& store, const char* str )
{
    auto aig = read_aiger( str );
    auto sys = builder::build_from_aiger( store, *aig );

    REQUIRE( sys.has_value() );

    return *sys;
}

}

TEST_CASE( "System with an unsafe initial state" )
{
    // 0 -> 1, 0 initial, 0 error
    const auto* const str =
            "aag 1 0 1 1 0\n"
            "2 1\n"
            "3\n";

    auto store = variable_store{};
    const auto system = system_from_aiger( store, str );

    auto checker = verifier{ store, system };
    const auto cex = checker.run();

    REQUIRE( cex.has_value() );
    REQUIRE( cex->size() == 1 );
    REQUIRE( cex->at( 0 ).empty() );
}

TEST_CASE( "Unsafe when input is true in the initial state" )
{
    // 0 -> 1, 0 initial, 0 error under input 1
    const auto* const str =
            "aag 2 1 1 1 0\n"
            "2\n"
            "4 1\n"
            "2\n";

    auto store = variable_store{};
    const auto system = system_from_aiger( store, str );

    auto checker = verifier{ store, system };
    const auto cex = checker.run();

    const auto i = literal{ system.input_vars().nth( 0 ) };

    REQUIRE( cex.has_value() );
    REQUIRE( cex->size() == 1 );
    REQUIRE( cex->at( 0 ) == std::vector{ i } );
}

TEST_CASE( "Unsafe when input is false in the initial state" )
{
    // 0 -> 1, 0 initial, 0 error under input 0
    const auto* const str =
            "aag 2 1 1 1 0\n"
            "2\n"
            "4 1\n"
            "3\n";

    auto store = variable_store{};
    const auto system = system_from_aiger( store, str );

    auto checker = verifier{ store, system };
    const auto cex = checker.run();

    const auto i = literal{ system.input_vars().nth( 0 ) };

    REQUIRE( cex.has_value() );
    REQUIRE( cex->size() == 1 );
    REQUIRE( cex->at( 0 ) == std::vector{ !i } );
}

TEST_CASE( "Unsafe state reached in one step" )
{
    // 0 -> 1, 0 initial, 1 error
    const auto* const str =
            "aag 1 0 1 1 0\n"
            "2 1\n"
            "2\n";

    auto store = variable_store{};
    const auto system = system_from_aiger( store, str );

    auto checker = verifier{ store, system };
    const auto cex = checker.run();

    // Actually technically two steps, the first brings us from 0 to 1 and
    // the second from 1 to "error".

    REQUIRE( cex.has_value() );
    REQUIRE( cex->size() == 2 );
    REQUIRE( cex->at( 0 ).empty() );
    REQUIRE( cex->at( 1 ).empty() );
}

TEST_CASE( "Unsafe four state system" )
{
    // 0 0 -> 1 0
    //  v      v
    // 0 1 -> 1 1
    //
    // x y = 0 0 is initial, 1 1 is error
    // Single input i: when 0, enable x, when 1, enable y

    const auto* const str =
            "aag 10 1 2 1 7\n"
            "2\n"         // i
            "4 19\n"      // x
            "6 21\n"      // y
            "12\n"        // error on x /\ y
            "8 5 3\n"     // -x /\ -i
            "10 7 2\n"    // -y /\ i
            "12 4 6\n"    // x /\ y
            "14 4 2\n"    // x /\ i
            "16 6 3\n"    // y /\ -i
            "18 9 15\n"   // -[ (-x /\ -i) \/ (x /\ i) ]
            "20 11 17\n"; // -[ (-y /\ i) \/ (y /\ -i) ]

    auto store = variable_store{};
    const auto system = system_from_aiger( store, str );

    auto checker = verifier{ store, system };
    const auto cex = checker.run();

    const auto i = literal{ system.input_vars().nth( 0 ) };

    REQUIRE( cex.has_value() );
    REQUIRE( cex->size() == 3 );

    const auto upper_path =
                cex->at( 0 ) == std::vector{ !i } &&
                cex->at( 1 ) == std::vector{ i };

    const auto lower_path =
            cex->at( 0 ) == std::vector{ i } &&
            cex->at( 1 ) == std::vector{ !i };

    REQUIRE( ( upper_path || lower_path ) );
}

TEST_CASE( "Trivially safe four state system" )
{
    const auto* const str =
                "aag 10 1 2 1 7\n"
                "2\n"         // i
                "4 19\n"      // x
                "6 21\n"      // y
                "0\n"         // error is False
                "8 5 3\n"     // -x /\ -i
                "10 7 2\n"    // -y /\ i
                "12 4 6\n"    // x /\ y
                "14 4 2\n"    // x /\ i
                "16 6 3\n"    // y /\ -i
                "18 9 15\n"   // -[ (-x /\ -i) \/ (x /\ i) ]
                "20 11 17\n"; // -[ (-y /\ i) \/ (y /\ -i) ]

    auto store = variable_store{};
    const auto system = system_from_aiger( store, str );

    auto checker = verifier{ store, system };
    const auto cex = checker.run();

    REQUIRE( !cex.has_value() );
}

TEST_CASE( "Unsafe state is not reachable in a two state system" )
{
    // States 0 and 1, self loops, 0 initial, 1 error
    const auto* const str =
            "aag 1 0 1 1 0\n"
            "2 2\n"
            "2\n";

    auto store = variable_store{};
    const auto system = system_from_aiger( store, str );

    auto checker = verifier{ store, system };
    const auto cex = checker.run();

    REQUIRE( !cex.has_value() );
}

TEST_CASE( "Simple counter with an error after 16 steps" )
{
    const auto* const str =
        "aag 16 0 4 0 12 1\n"
        "2 18\n"
        "4 22\n"
        "6 26\n"
        "8 9\n"
        "32\n"
        "10 8 6\n"
        "12 10 4\n"
        "14 12 2\n"
        "16 13 3\n"
        "18 17 15\n"
        "20 11 5\n"
        "22 21 13\n"
        "24 9 7\n"
        "26 25 11\n"
        "28 4 2\n"
        "30 28 6\n"
        "32 30 8\n";

    auto store = variable_store{};
    const auto system = system_from_aiger( store, str );

    auto checker = verifier{ store, system };
    const auto cex = checker.run();

    REQUIRE( cex.has_value() );
    REQUIRE( cex->size() == 16 );

    REQUIRE( system.initial_cube() == std::vector< bool >( 4, false ) );
    REQUIRE( std::ranges::all_of( *cex, []( const std::vector< literal >& inputs ){ return inputs.empty(); } ) );
}
