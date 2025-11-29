#pragma once

#include "logic.hpp"
#include <vector>
#include <utility>

enum class var_type
{
    input,
    state,
    next_state,
    auxiliary
};

class transition_system
{
    // The transition system consists of 3 formulas. The initial formula _init
    // describes the initial states, the error formula _error describes the bad
    // states and the transition formula _trans describes the transition
    // relation. The formulas _init and _error range over state variables, and
    // _trans ranges over those as well, plus the primed (next) state variables
    // and the input variables. In addition, all three formulas might contain
    // additional auxiliary Tseitin variables.

    variable_range _input_vars;
    variable_range _state_vars;
    variable_range _next_state_vars;
    variable_range _aux_vars;

    // Since _input_vars does not contain all the variables appearing in the
    // original aiger file (some might have been removed since they are not
    // in the cone of influence of the error formula), we need to remember the
    // whole initial cube as given in the aiger file (and in the same order)
    // to print the initial state of the counterexample trace.

    std::vector< bool > _initial_cube;

    cnf_formula _init;
    cnf_formula _trans;
    cnf_formula _error;

public:
    transition_system( variable_range input_vars, variable_range state_vars, variable_range next_state_vars,
                       variable_range aux_vars, std::vector< bool > init_cube, cnf_formula init,
                       cnf_formula trans, cnf_formula error )
            : _input_vars{ input_vars }, _state_vars{ state_vars }, _next_state_vars{ next_state_vars },
              _aux_vars{ aux_vars }, _initial_cube( std::move( init_cube ) ), _init{ std::move( init ) },
              _trans{ std::move( trans ) }, _error{ std::move( error ) }
    {
        assert( state_vars.size() == next_state_vars.size() );
    }

    [[nodiscard]] variable_range input_vars() const { return _input_vars; };
    [[nodiscard]] variable_range state_vars() const { return _state_vars; };
    [[nodiscard]] variable_range next_state_vars() const { return _next_state_vars; };
    [[nodiscard]] variable_range aux_vars() const { return _aux_vars; }

    [[nodiscard]] const std::vector< bool >& initial_cube() const { return _initial_cube; }

    [[nodiscard]] const cnf_formula& init() const { return _init; }
    [[nodiscard]] const cnf_formula& trans() const { return _trans; }
    [[nodiscard]] const cnf_formula& error() const { return _error; }

    // Returns the type of the variable and its position within the respective
    // variable range.
    [[nodiscard]] std::pair< var_type, int > get_var_info( variable var ) const
    {
        if ( _input_vars.contains( var ) )
            return { var_type::input, _input_vars.offset( var ) };
        if ( _state_vars.contains( var ) )
            return { var_type::state, _state_vars.offset( var ) };
        if ( _next_state_vars.contains( var ) )
            return { var_type::next_state, _next_state_vars.offset( var ) };
        if ( _aux_vars.contains( var ) )
            return { var_type::auxiliary, _aux_vars.offset( var ) };

        assert( false && "Unreachable code reached" );
        std::unreachable();
    }

    // TODO: Do we need these?
    [[nodiscard]] literal prime( literal lit ) const
    {
        const auto [ type, pos ] = get_var_info( lit.var() );
        assert( type == var_type::state );

        return lit.substitute( _next_state_vars.nth( pos ) );
    }

    [[nodiscard]] literal unprime( literal lit ) const
    {
        const auto [ type, pos ] = get_var_info( lit.var() );
        assert( type == var_type::next_state );

        return lit.substitute( _state_vars.nth( pos ) );
    }
};
