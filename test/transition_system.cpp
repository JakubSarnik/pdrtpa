#include "common.hpp"
#include "logic.hpp"
#include "transition_system.hpp"

namespace
{

transition_system make_system( int input_vars, int state_vars, int aux_vars )
{
    auto store = variable_store{};

    return { store.make_range( input_vars ), store.make_range( state_vars ),
        store.make_range( state_vars ), store.make_range( aux_vars ),
        std::vector( state_vars, false ), cnf_formula{}, cnf_formula{}, cnf_formula{} };
}

}

TEST_CASE( "Variable types and positions are correctly determined" )
{
    SECTION( "Only state variables" )
    {
        const auto system = make_system( 0, 2, 0 );

        {
            const auto [ type, pos ] = system.get_var_info( system.state_vars().nth( 0 ) );

            REQUIRE( type == var_type::state );
            REQUIRE( pos == 0 );
        }

        {
            const auto [ type, pos ] = system.get_var_info( system.state_vars().nth( 1 ) );

            REQUIRE( type == var_type::state );
            REQUIRE( pos == 1 );
        }

        {
            const auto [ type, pos ] = system.get_var_info( system.next_state_vars().nth( 0 ) );

            REQUIRE( type == var_type::next_state );
            REQUIRE( pos == 0 );
        }

        {
            const auto [ type, pos ] = system.get_var_info( system.next_state_vars().nth( 1 ) );

            REQUIRE( type == var_type::next_state );
            REQUIRE( pos == 1 );
        }
    }

    SECTION( "All types of variables" )
    {
        const auto system = make_system( 3, 2, 5 );

        {
            const auto [ type, pos ] = system.get_var_info( system.input_vars().nth( 0 ) );

            REQUIRE( type == var_type::input );
            REQUIRE( pos == 0 );
        }

        {
            const auto [ type, pos ] = system.get_var_info( system.state_vars().nth( 1 ) );

            REQUIRE( type == var_type::state );
            REQUIRE( pos == 1 );
        }

        {
            const auto [ type, pos ] = system.get_var_info( system.next_state_vars().nth( 0 ) );

            REQUIRE( type == var_type::next_state );
            REQUIRE( pos == 0 );
        }

        {
            const auto [ type, pos ] = system.get_var_info( system.aux_vars().nth( 0 ) );

            REQUIRE( type == var_type::auxiliary );
            REQUIRE( pos == 0 );
        }

        {
            const auto [ type, pos ] = system.get_var_info( system.aux_vars().nth( 3 ) );

            REQUIRE( type == var_type::auxiliary );
            REQUIRE( pos == 3 );
        }
    }
}
