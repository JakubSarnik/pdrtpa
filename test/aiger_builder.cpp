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
    const auto input = literal{ ctx.input_vars.nth( 0 ) };

    SECTION( "Context is set up correctly" )
    {
        check_sizes( ctx, {
            .input_vars = 1,
            .state_vars = 0,
            .next_state_vars = 0,
            .and_vars = 0
        } );

        REQUIRE( from_aiger_lit( ctx, 2 ) == input );
        REQUIRE( from_aiger_lit( ctx, 3 ) == !input );
    }

    SECTION( "The transition system is correct" )
    {
        const auto system = expected_system
        {
            .init = {},
            .trans = {},
            .error = { input, literal::separator },
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
    const auto input = literal{ ctx.input_vars.nth( 0 ) };

    SECTION( "Context is set up correctly" )
    {
        check_sizes( ctx, {
                .input_vars = 1,
                .state_vars = 0,
                .next_state_vars = 0,
                .and_vars = 0
        } );

        REQUIRE( from_aiger_lit( ctx, 2 ) == input );
        REQUIRE( from_aiger_lit( ctx, 3 ) == !input );
    }

    SECTION( "The transition system is correct" )
    {
        const auto system = expected_system
        {
            .init = {},
            .trans = {},
            .error = { !input, literal::separator },
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
    const auto x = literal{ ctx.input_vars.nth( 0 ) };
    const auto y = literal{ ctx.input_vars.nth( 1 ) };
    const auto z = literal{ ctx.and_vars.nth( 0 ) };
    const auto s = literal::separator;

    SECTION( "Context is set up correctly" )
    {
        check_sizes( ctx, {
                .input_vars = 2,
                .state_vars = 0,
                .next_state_vars = 0,
                .and_vars = 1
        } );

        REQUIRE( from_aiger_lit( ctx, 2 ) == x );
        REQUIRE( from_aiger_lit( ctx, 3 ) == !x );
        REQUIRE( from_aiger_lit( ctx, 4 ) == y );
        REQUIRE( from_aiger_lit( ctx, 5 ) == !y );
        REQUIRE( from_aiger_lit( ctx, 6 ) == z );
        REQUIRE( from_aiger_lit( ctx, 7 ) == !z );
    }

    SECTION( "The transition system is correct" )
    {
        // Inputs: x (1), y (2)
        // Ands: z (3)
        // Original formula: z = y /\ x [output z]
        // As implications: (z -> y) /\ (z -> x) /\ (y /\ x -> z)
        // Our formula: (-z \/ y) /\ (-z \/ x) /\ (-y \/ -x \/ z)

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
    const auto x = literal{ ctx.input_vars.nth( 0 ) };
    const auto y = literal{ ctx.input_vars.nth( 1 ) };
    const auto z = literal{ ctx.and_vars.nth( 0 ) };
    const auto s = literal::separator;

    SECTION( "Context is set up correctly" )
    {
        check_sizes( ctx, {
                .input_vars = 2,
                .state_vars = 0,
                .next_state_vars = 0,
                .and_vars = 1
        } );

        REQUIRE( from_aiger_lit( ctx, 2 ) == x );
        REQUIRE( from_aiger_lit( ctx, 3 ) == !x );
        REQUIRE( from_aiger_lit( ctx, 4 ) == y );
        REQUIRE( from_aiger_lit( ctx, 5 ) == !y );
        REQUIRE( from_aiger_lit( ctx, 6 ) == z );
        REQUIRE( from_aiger_lit( ctx, 7 ) == !z );
    }

    SECTION( "The transition system is correct" )
    {
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

TEST_CASE( "Constant latch initialized with false" )
{
    const auto* const str =
            "aag 1 0 1 1 0\n"
            "2 2\n"
            "2\n";

    auto aig = read_aiger( str );
    auto store = variable_store{};

    auto info = make_aiger_info( *aig );
    REQUIRE( info.has_value() );
    REQUIRE( info->aig == aig.get() );
    REQUIRE( info->true_literals == std::unordered_set< aiger_literal >{ aiger_true } );
    REQUIRE( info->error_coi == std::unordered_set< aiger_literal >{ 2 } );

    auto ctx = make_context( store, *info );
    const auto x = literal{ ctx.state_vars.nth( 0 ) };
    const auto xp = literal{ ctx.next_state_vars.nth( 0 ) };
    const auto s = literal::separator;

    SECTION( "Context is set up correctly" )
    {
        check_sizes( ctx, {
                .input_vars = 0,
                .state_vars = 1,
                .next_state_vars = 1,
                .and_vars = 0
        } );

        REQUIRE( from_aiger_lit( ctx, 2 ) == x );
        REQUIRE( from_aiger_lit( ctx, 3 ) == !x );
    }

    SECTION( "The transition system is correct" )
    {
        const auto system = expected_system
        {
            .init = { !x, s },                 // -x
            .trans = { !xp, x, s, !x, xp, s }, // x' = x (i.e. (-x' \/ x) /\ (-x \/ x'))
            .error = { x, s },                 // x
            .initial_cube = { false }
        };

        check_system( ctx, system );
    }
}

TEST_CASE( "Constant latch initialized with true" )
{
    const auto* const str =
            "aag 1 0 1 1 0\n"
            "2 2 1\n"
            "2\n";

    auto aig = read_aiger( str );
    auto store = variable_store{};

    auto info = make_aiger_info( *aig );
    REQUIRE( info.has_value() );
    REQUIRE( info->aig == aig.get() );
    REQUIRE( info->true_literals == std::unordered_set< aiger_literal >{ aiger_true } );
    REQUIRE( info->error_coi == std::unordered_set< aiger_literal >{ 2 } );

    auto ctx = make_context( store, *info );
    const auto x = literal{ ctx.state_vars.nth( 0 ) };
    const auto xp = literal{ ctx.next_state_vars.nth( 0 ) };
    const auto s = literal::separator;

    SECTION( "Context is set up correctly" )
    {
        check_sizes( ctx, {
                .input_vars = 0,
                .state_vars = 1,
                .next_state_vars = 1,
                .and_vars = 0
        } );

        REQUIRE( from_aiger_lit( ctx, 2 ) == x );
        REQUIRE( from_aiger_lit( ctx, 3 ) == !x );
    }

    SECTION( "The transition system is correct" )
    {
        const auto system = expected_system
        {
            .init = { x, s },                  // x
            .trans = { !xp, x, s, !x, xp, s }, // x' = x (i.e. (-x' \/ x) /\ (-x \/ x'))
            .error = { x, s },                 // x
            .initial_cube = { true }
        };

        check_system( ctx, system );
    }
}

TEST_CASE( "Simple flip flop" )
{
    const auto* const str =
            "aag 1 0 1 1 0\n"
            "2 3\n"
            "2\n";

    auto aig = read_aiger( str );
    auto store = variable_store{};

    auto info = make_aiger_info( *aig );
    REQUIRE( info.has_value() );
    REQUIRE( info->aig == aig.get() );
    REQUIRE( info->true_literals == std::unordered_set< aiger_literal >{ aiger_true } );
    REQUIRE( info->error_coi == std::unordered_set< aiger_literal >{ 2 } );

    auto ctx = make_context( store, *info );
    const auto x = literal{ ctx.state_vars.nth( 0 ) };
    const auto xp = literal{ ctx.next_state_vars.nth( 0 ) };
    const auto s = literal::separator;

    SECTION( "Context is set up correctly" )
    {
        check_sizes( ctx, {
                .input_vars = 0,
                .state_vars = 1,
                .next_state_vars = 1,
                .and_vars = 0
        } );

        REQUIRE( from_aiger_lit( ctx, 2 ) == x );
        REQUIRE( from_aiger_lit( ctx, 3 ) == !x );
    }

    SECTION( "The transition system is correct" )
    {
        const auto system = expected_system
        {
            .init = { !x, s },                 // -x
            .trans = { !xp, !x, s, x, xp, s }, // x' = -x (i.e. (-x' \/ -x) /\ (x \/ x'))
            .error = { x, s },                 // x
            .initial_cube = { false }
        };

        check_system( ctx, system );
    }
}

TEST_CASE( "Simple flip flop with indeterminate initial state" )
{
    const auto* const str =
            "aag 1 0 1 1 0\n"
            "2 3 2\n"
            "2\n";

    auto aig = read_aiger( str );
    auto store = variable_store{};

    auto info = make_aiger_info( *aig );
    REQUIRE( info.has_value() );
    REQUIRE( info->aig == aig.get() );
    REQUIRE( info->true_literals == std::unordered_set< aiger_literal >{ aiger_true } );
    REQUIRE( info->error_coi == std::unordered_set< aiger_literal >{ 2 } );

    auto ctx = make_context( store, *info );
    const auto x = literal{ ctx.state_vars.nth( 0 ) };
    const auto xp = literal{ ctx.next_state_vars.nth( 0 ) };
    const auto s = literal::separator;

    SECTION( "Context is set up correctly" )
    {
        check_sizes( ctx, {
                .input_vars = 0,
                .state_vars = 1,
                .next_state_vars = 1,
                .and_vars = 0
        } );

        REQUIRE( from_aiger_lit( ctx, 2 ) == x );
        REQUIRE( from_aiger_lit( ctx, 3 ) == !x );
    }

    SECTION( "The transition system is correct" )
    {
        const auto system = expected_system
        {
            .init = {},                        // True
            .trans = { !xp, !x, s, x, xp, s }, // x' = -x (i.e. (-x' \/ -x) /\ (x \/ x'))
            .error = { x, s },                 // x
            .initial_cube = {}
        };

        check_system( ctx, system );
    }
}

TEST_CASE( "More complicated flip flop" )
{
    const auto* const str =
            "aag 7 2 1 1 4\n"
            "2\n"
            "4\n"
            "6 14\n"
            "6\n"
            "8 6 2\n"
            "10 7 3\n"
            "12 11 9\n"
            "14 12 4\n";

    auto aig = read_aiger( str );
    auto store = variable_store{};

    auto info = make_aiger_info( *aig );
    REQUIRE( info.has_value() );
    REQUIRE( info->aig == aig.get() );
    REQUIRE( info->true_literals == std::unordered_set< aiger_literal >{ aiger_true } );
    REQUIRE( info->error_coi == std::unordered_set< aiger_literal >{ 6 } );

    auto ctx = make_context( store, *info );
    const auto y0 = literal{ ctx.input_vars.nth( 0 ) };
    const auto y1 = literal{ ctx.input_vars.nth( 1 ) };
    const auto x0 = literal{ ctx.state_vars.nth( 0 ) };
    const auto x0p = literal{ ctx.next_state_vars.nth( 0 ) };
    const auto a0 = literal{ ctx.and_vars.nth( 0 ) };
    const auto a1 = literal{ ctx.and_vars.nth( 1 ) };
    const auto a2 = literal{ ctx.and_vars.nth( 2 ) };
    const auto a3 = literal{ ctx.and_vars.nth( 3 ) };
    const auto s = literal::separator;

    SECTION( "Context is set up correctly" )
    {
        check_sizes( ctx, {
                .input_vars = 2,
                .state_vars = 1,
                .next_state_vars = 1,
                .and_vars = 4
        } );

        REQUIRE( from_aiger_lit( ctx, 2 ) == y0 );
        REQUIRE( from_aiger_lit( ctx, 3 ) == !y0 );
        REQUIRE( from_aiger_lit( ctx, 4 ) == y1 );
        REQUIRE( from_aiger_lit( ctx, 5 ) == !y1 );

        REQUIRE( from_aiger_lit( ctx, 6 ) == x0 );
        REQUIRE( from_aiger_lit( ctx, 7 ) == !x0 );

        REQUIRE( from_aiger_lit( ctx, 8 ) == a0 );
        REQUIRE( from_aiger_lit( ctx, 9 ) == !a0 );
        REQUIRE( from_aiger_lit( ctx, 10 ) == a1 );
        REQUIRE( from_aiger_lit( ctx, 11 ) == !a1 );
        REQUIRE( from_aiger_lit( ctx, 12 ) == a2 );
        REQUIRE( from_aiger_lit( ctx, 13 ) == !a2 );
        REQUIRE( from_aiger_lit( ctx, 14 ) == a3 );
        REQUIRE( from_aiger_lit( ctx, 15 ) == !a3 );
    }

    SECTION( "The transition system is correct" )
    {
        // a3  =  a2  /\  y1
        // a2  = -a1  /\ -a0
        // a1  = -x0  /\ -y0
        // a0  =  x0  /\  y0
        // x'0 =  a3

        // (a3  ->  a2) /\ (a3 ->  y1) /\ ( a2 /\  y1 -> a3) /\
        // (a2  -> -a1) /\ (a2 -> -a0) /\ (-a1 /\ -a0 -> a2) /\
        // (a1  -> -x0) /\ (a1 -> -y0) /\ (-x0 /\ -y0 -> a1) /\
        // (a0  ->  x0) /\ (a0 ->  y0) /\ ( x0 /\  y0 -> a0) /\
        // (x'0 ->  a3) /\ (a3 -> x'0)

        // (-a3  \/  a2) /\ (-a3 \/  y1) /\ (-a2 \/ -y1 \/ a3)
        // (-a2  \/ -a1) /\ (-a2 \/ -a0) /\ ( a1 \/  a0 \/ a2)
        // (-a1  \/ -x0) /\ (-a1 \/ -y0) /\ ( x0 \/  y0 \/ a1)
        // (-a0  \/  x0) /\ (-a0 \/  y0) /\ (-x0 \/ -y0 \/ a0)
        // (-x'0 \/  a3) /\ (-a3 \/ x'0)

        const auto system = expected_system
        {
            .init = { !x0, s },
            .trans =
            {
                 !a3,  a2, s, !a3,  y1, s, !a2, !y1, a3, s,
                 !a2, !a1, s, !a2, !a0, s,  a1,  a0, a2, s,
                 !a1, !x0, s, !a1, !y0, s,  x0,  y0, a1, s,
                 !a0,  x0, s, !a0,  y0, s, !x0, !y0, a0, s,
                !x0p,  a3, s, !a3, x0p, s
            },
            .error = { x0, s },
            .initial_cube = { false }
        };

        check_system( ctx, system );
    }
}

TEST_CASE( "More complicated flip flop with negated next state function" )
{
    const auto* const str =
            "aag 7 2 1 1 4\n"
            "2\n"
            "4\n"
            "6 15\n"
            "6\n"
            "8 6 2\n"
            "10 7 3\n"
            "12 11 9\n"
            "14 12 4\n";

    auto aig = read_aiger( str );
    auto store = variable_store{};

    auto info = make_aiger_info( *aig );
    REQUIRE( info.has_value() );
    REQUIRE( info->aig == aig.get() );
    REQUIRE( info->true_literals == std::unordered_set< aiger_literal >{ aiger_true } );
    REQUIRE( info->error_coi == std::unordered_set< aiger_literal >{ 6 } );

    auto ctx = make_context( store, *info );
    const auto y0 = literal{ ctx.input_vars.nth( 0 ) };
    const auto y1 = literal{ ctx.input_vars.nth( 1 ) };
    const auto x0 = literal{ ctx.state_vars.nth( 0 ) };
    const auto x0p = literal{ ctx.next_state_vars.nth( 0 ) };
    const auto a0 = literal{ ctx.and_vars.nth( 0 ) };
    const auto a1 = literal{ ctx.and_vars.nth( 1 ) };
    const auto a2 = literal{ ctx.and_vars.nth( 2 ) };
    const auto a3 = literal{ ctx.and_vars.nth( 3 ) };
    const auto s = literal::separator;

    // a3  =  a2  /\  y1
    // a2  = -a1  /\ -a0
    // a1  = -x0  /\ -y0
    // a0  =  x0  /\  y0
    // x'0 = -a3

    // (a3  ->  a2) /\ ( a3 ->  y1) /\ ( a2 /\  y1 -> a3) /\
    // (a2  -> -a1) /\ ( a2 -> -a0) /\ (-a1 /\ -a0 -> a2) /\
    // (a1  -> -x0) /\ ( a1 -> -y0) /\ (-x0 /\ -y0 -> a1) /\
    // (a0  ->  x0) /\ ( a0 ->  y0) /\ ( x0 /\  y0 -> a0) /\
    // (x'0 -> -a3) /\ (-a3 -> x'0)

    // (-a3  \/  a2) /\ (-a3 \/  y1) /\ (-a2 \/ -y1 \/ a3)
    // (-a2  \/ -a1) /\ (-a2 \/ -a0) /\ ( a1 \/  a0 \/ a2)
    // (-a1  \/ -x0) /\ (-a1 \/ -y0) /\ ( x0 \/  y0 \/ a1)
    // (-a0  \/  x0) /\ (-a0 \/  y0) /\ (-x0 \/ -y0 \/ a0)
    // (-x'0 \/ -a3) /\ ( a3 \/ x'0)

    const auto system = expected_system
    {
        .init = { !x0, s },
        .trans =
        {
            !a3,  a2, s, !a3,  y1, s, !a2, !y1, a3, s,
            !a2, !a1, s, !a2, !a0, s,  a1,  a0, a2, s,
            !a1, !x0, s, !a1, !y0, s,  x0,  y0, a1, s,
            !a0,  x0, s, !a0,  y0, s, !x0, !y0, a0, s,
           !x0p, !a3, s,  a3, x0p, s
       },
       .error = { x0, s },
       .initial_cube = { false }
    };

    check_system( ctx, system );
}

TEST_CASE( "Constant false state variable is removed from the system" )
{
    const auto* const str =
            "aag 2 0 1 1 1\n"
            "2 4\n"
            "2\n"
            "4 2 0\n";

    auto aig = read_aiger( str );
    auto store = variable_store{};

    auto info = make_aiger_info( *aig );
    REQUIRE( info.has_value() );
    REQUIRE( info->aig == aig.get() );
    REQUIRE( info->true_literals == std::unordered_set< aiger_literal >{ aiger_true, 3, 5 } );
    REQUIRE( info->error_coi.empty() );

    auto ctx = make_context( store, *info );
    const auto s = literal::separator;

    SECTION( "Context is set up correctly" )
    {
        check_sizes( ctx, {
                .input_vars = 0,
                .state_vars = 0,
                .next_state_vars = 0,
                .and_vars = 1
        } );
    }

    SECTION( "The transition system is correct" )
    {
        const auto system = expected_system
        {
            .init = {},     // True
            .trans = {},    // True
            .error = { s }, // False
            .initial_cube = { false }
        };

        check_system( ctx, system );
    }
}

TEST_CASE( "Constant true state variable is removed from the system" )
{
    const auto* const str =
            "aag 2 0 1 1 1\n"
            "2 5 1\n"
            "2\n"
            "4 2 0\n";

    auto aig = read_aiger( str );
    auto store = variable_store{};

    auto info = make_aiger_info( *aig );
    REQUIRE( info.has_value() );
    REQUIRE( info->aig == aig.get() );
    REQUIRE( info->true_literals == std::unordered_set< aiger_literal >{ aiger_true, 2, 5 } );
    REQUIRE( info->error_coi.empty() );

    auto ctx = make_context( store, *info );

    SECTION( "Context is set up correctly" )
    {
        check_sizes( ctx, {
                .input_vars = 0,
                .state_vars = 0,
                .next_state_vars = 0,
                .and_vars = 1
        } );
    }

    SECTION( "The transition system is correct" )
    {
        const auto system = expected_system
        {
            .init = {},  // True
            .trans = {}, // True
            .error = {}, // True
            .initial_cube = { true }
        };

        check_system( ctx, system );
    }
}

TEST_CASE( "Variable with constant next state but differing initial state is kept" )
{
    const auto* const str =
            "aag 2 0 1 1 1\n"
            "2 5 0\n"
            "2\n"
            "4 2 0\n";

    auto aig = read_aiger( str );
    auto store = variable_store{};

    auto info = make_aiger_info( *aig );
    REQUIRE( info.has_value() );
    REQUIRE( info->aig == aig.get() );
    REQUIRE( info->true_literals == std::unordered_set< aiger_literal >{ aiger_true, 5 } );
    REQUIRE( info->error_coi == std::unordered_set< aiger_literal >{ 2 } );

    auto ctx = make_context( store, *info );
    const auto x = literal{ ctx.state_vars.nth( 0 ) };
    const auto xp = literal{ ctx.next_state_vars.nth( 0 ) };
    const auto s = literal::separator;

    SECTION( "Context is set up correctly" )
    {
        check_sizes( ctx, {
                .input_vars = 0,
                .state_vars = 1,
                .next_state_vars = 1,
                .and_vars = 1
        } );
    }

    SECTION( "The transition system is correct" )
    {
        const auto system = expected_system
        {
            .init = { !x, s },  // !x
            .trans = { xp, s }, // x' = True
            .error = { x, s },  // x
            .initial_cube = { false }
        };

        check_system( ctx, system );
    }
}

TEST_CASE( "Variable that cannot influence the error is removed" )
{
    const auto* const str =
            "aag 3 0 2 1 1\n"
            "2 3\n"
            "4 6 1\n"
            "2\n"
            "6 2 5\n";

    auto aig = read_aiger( str );
    auto store = variable_store{};

    auto info = make_aiger_info( *aig );
    REQUIRE( info.has_value() );
    REQUIRE( info->aig == aig.get() );
    REQUIRE( info->true_literals == std::unordered_set< aiger_literal >{ aiger_true } );
    REQUIRE( info->error_coi == std::unordered_set< aiger_literal >{ 2 } );

    auto ctx = make_context( store, *info );
    const auto x = literal{ ctx.state_vars.nth( 0 ) };
    const auto xp = literal{ ctx.next_state_vars.nth( 0 ) };
    const auto s = literal::separator;

    SECTION( "Context is set up correctly" )
    {
        check_sizes( ctx, {
                .input_vars = 0,
                .state_vars = 1,
                .next_state_vars = 1,
                .and_vars = 1
        } );

        REQUIRE( from_aiger_lit( ctx, 2 ) == x );
        REQUIRE( from_aiger_lit( ctx, 3 ) == !x );
    }

    SECTION( "The transition system is correct" )
    {
        const auto system = expected_system
        {
            .init = { !x, s },                 // -x
            .trans = { !xp, !x, s, x, xp, s }, // x' = -x (i.e. (-x' \/ -x) /\ (x \/ x'))
            .error = { x, s },                 // x
            .initial_cube = { false, true }
        };

        check_system( ctx, system );
    }
}
