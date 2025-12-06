#include "common.hpp"
#include "aiger_builder.hpp"

using namespace builder;

namespace
{

using aiger_ptr = std::unique_ptr< aiger, decltype( &aiger_reset ) >;

aiger_ptr make_aiger()
{
    return { aiger_init(), &aiger_reset };
}

aiger_ptr read_aiger( const char* str )
{
    auto aig = make_aiger();
    const auto* const err = aiger_read_from_string( aig.get(), str );

    REQUIRE( err == nullptr );

    return aig;
}

struct expected_system
{
    std::vector< literal > init;
    std::vector< literal > trans;
    std::vector< literal > error;

    std::vector< bool > initial_cube;
};

void check_system( context& ctx, const expected_system& expected )
{
    const auto res = build_from_context( ctx );

    REQUIRE( res.init().literals() == expected.init );
    REQUIRE( res.trans().literals() == expected.trans );
    REQUIRE( res.error().literals() == expected.error );
    REQUIRE( res.initial_cube() == expected.initial_cube );
}

struct expected_counts
{
    int input_vars;
    int state_vars;
    int next_state_vars;
    int and_vars;
};

void check_sizes( const context& ctx, const expected_counts& expected )
{
    REQUIRE( ctx.input_vars.size() == expected.input_vars );
    REQUIRE( ctx.state_vars.size() == expected.state_vars );
    REQUIRE( ctx.next_state_vars.size() == expected.next_state_vars );
    REQUIRE( ctx.and_vars.size() == expected.and_vars );
}

}

// ASCII Aiger files pre 1.9 have the following header:
// aag M I L O A, where
//   M = maximum variable index
//   I = number of inputs
//   L = number of latches
//   O = number of outputs
//   A = number of AND gates
// MAKE SURE that all the AIGs here are reencoded, so that the variable
// numberings and order of operands isn't changed by make_context.

TEST_CASE( "Empty aig" )
{
    auto aig = read_aiger( "aag 0 0 0 0 0\n" );

    auto store = variable_store{};
    auto res = build_from_aiger( store, *aig );

    REQUIRE( !res.has_value() );
}

TEST_CASE( "Buffer gate" )
{
    const auto* const str =
        "aag 1 1 0 1 0\n"
        "2\n"
        "2\n";

    auto aig = read_aiger( str );
    auto store = variable_store{};

    auto info = make_aiger_info( *aig );
    REQUIRE( info.has_value() );
    REQUIRE( info->aig == aig.get() );
    REQUIRE( info->true_literals == std::unordered_set< aiger_literal >{ aiger_true } );
    REQUIRE( info->error_coi.empty() );

    auto ctx = make_context( store, *info );

    SECTION( "Context is set up correctly" )
    {
        check_sizes( ctx, {
            .input_vars = 1,
            .state_vars = 0,
            .next_state_vars = 0,
            .and_vars = 0
        } );

        const auto input = literal{ ctx.input_vars.nth( 0 ) };

        REQUIRE( from_aiger_lit( ctx, 2 ) == input );
        REQUIRE( from_aiger_lit( ctx, 3 ) == !input );
    }

    SECTION( "The transition system is correct" )
    {
        const auto system = expected_system
        {
            .init = {},
            .trans = {},
            .error = { literal{ ctx.input_vars.nth( 0 ) }, literal::separator },
            .initial_cube = {}
        };

        check_system( ctx, system );
    }
}

TEST_CASE( "Inverter gate" )
{
    const auto* const str =
            "aag 1 1 0 1 0\n"
            "2\n"
            "3\n";

    auto aig = read_aiger( str );
    auto store = variable_store{};

    auto info = make_aiger_info( *aig );
    REQUIRE( info.has_value() );
    REQUIRE( info->aig == aig.get() );
    REQUIRE( info->true_literals == std::unordered_set< aiger_literal >{ aiger_true } );
    REQUIRE( info->error_coi.empty() );

    auto ctx = make_context( store, *info );

    SECTION( "Context is set up correctly" )
    {
        check_sizes( ctx, {
                .input_vars = 1,
                .state_vars = 0,
                .next_state_vars = 0,
                .and_vars = 0
        } );

        const auto input = literal{ ctx.input_vars.nth( 0 ) };

        REQUIRE( from_aiger_lit( ctx, 2 ) == input );
        REQUIRE( from_aiger_lit( ctx, 3 ) == !input );
    }

    SECTION( "The transition system is correct" )
    {
        const auto system = expected_system
        {
            .init = {},
            .trans = {},
            .error = { !literal{ ctx.input_vars.nth( 0 ) }, literal::separator },
            .initial_cube = {}
        };

        check_system( ctx, system );
    }
}

TEST_CASE( "And gate" )
{
    const auto* const str =
            "aag 3 2 0 1 1\n"
            "2\n"
            "4\n"
            "6\n"
            "6 4 2\n";

    auto aig = read_aiger( str );
    auto store = variable_store{};

    auto info = make_aiger_info( *aig );
    REQUIRE( info.has_value() );
    REQUIRE( info->aig == aig.get() );
    REQUIRE( info->true_literals == std::unordered_set< aiger_literal >{ aiger_true } );
    REQUIRE( info->error_coi.empty() );

    auto ctx = make_context( store, *info );

    SECTION( "Context is set up correctly" )
    {
        check_sizes( ctx, {
                .input_vars = 2,
                .state_vars = 0,
                .next_state_vars = 0,
                .and_vars = 1
        } );

        const auto in0 = literal{ ctx.input_vars.nth( 0 ) };
        const auto in1 = literal{ ctx.input_vars.nth( 1 ) };
        const auto cnj = literal{ ctx.and_vars.nth( 0 ) };

        REQUIRE( from_aiger_lit( ctx, 2 ) == in0 );
        REQUIRE( from_aiger_lit( ctx, 3 ) == !in0 );
        REQUIRE( from_aiger_lit( ctx, 4 ) == in1 );
        REQUIRE( from_aiger_lit( ctx, 5 ) == !in1 );
        REQUIRE( from_aiger_lit( ctx, 6 ) == cnj );
        REQUIRE( from_aiger_lit( ctx, 7 ) == !cnj );
    }

    SECTION( "The transition system is correct" )
    {
        // Inputs: x (1), y (2)
        // Ands: z (3)
        // Original formula: z = y /\ x [output z]
        // As implications: (z -> y) /\ (z -> x) /\ (y /\ x -> z)
        // Our formula: (-z \/ y) /\ (-z \/ x) /\ (-y \/ -x \/ z)

        const auto x = literal{ ctx.input_vars.nth( 0 ) };
        const auto y = literal{ ctx.input_vars.nth( 1 ) };
        const auto z = literal{ ctx.and_vars.nth( 0 ) };
        const auto s = literal::separator;

        const auto system = expected_system
        {
            .init = {},
            .trans = {},
            .error = { !z, y, s, !z, x, s, !y, !x, z, s, z, s },
            .initial_cube = {}
        };

        check_system( ctx, system );
    }
}

TEST_CASE( "Or gate" )
{
    const auto* const str =
            "aag 3 2 0 1 1\n"
            "2\n"
            "4\n"
            "7\n"
            "6 5 3\n";

    auto aig = read_aiger( str );
    auto store = variable_store{};

    auto info = make_aiger_info( *aig );
    REQUIRE( info.has_value() );
    REQUIRE( info->aig == aig.get() );
    REQUIRE( info->true_literals == std::unordered_set< aiger_literal >{ aiger_true } );
    REQUIRE( info->error_coi.empty() );

    auto ctx = make_context( store, *info );

    SECTION( "Context is set up correctly" )
    {
        check_sizes( ctx, {
                .input_vars = 2,
                .state_vars = 0,
                .next_state_vars = 0,
                .and_vars = 1
        } );

        const auto in0 = literal{ ctx.input_vars.nth( 0 ) };
        const auto in1 = literal{ ctx.input_vars.nth( 1 ) };
        const auto cnj = literal{ ctx.and_vars.nth( 0 ) };

        REQUIRE( from_aiger_lit( ctx, 2 ) == in0 );
        REQUIRE( from_aiger_lit( ctx, 3 ) == !in0 );
        REQUIRE( from_aiger_lit( ctx, 4 ) == in1 );
        REQUIRE( from_aiger_lit( ctx, 5 ) == !in1 );
        REQUIRE( from_aiger_lit( ctx, 6 ) == cnj );
        REQUIRE( from_aiger_lit( ctx, 7 ) == !cnj );
    }

    SECTION( "The transition system is correct" )
    {
        const auto x = literal{ ctx.input_vars.nth( 0 ) };
        const auto y = literal{ ctx.input_vars.nth( 1 ) };
        const auto z = literal{ ctx.and_vars.nth( 0 ) };
        const auto s = literal::separator;

        const auto system = expected_system
        {
            .init = {},
            .trans = {},
            .error = { !z, !y, s, !z, !x, s, y, x, z, s, !z, s },
            .initial_cube = {}
        };

        check_system( ctx, system );
    }
}
