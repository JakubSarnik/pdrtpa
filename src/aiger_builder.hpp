#pragma once

#include "logic.hpp"
#include "transition_system.hpp"
#include "aiger.h"
#include <unordered_set>
#include <unordered_map>
#include <expected>
#include <string>

namespace builder
{

using aiger_literal = unsigned int;

// Aiger files are first preprocessed to compute both the set of variables that
// are constant throughout the computation (x is in true_literals if x is
// constantly true, ~x is in true_literals is x is constantly false) and the
// set of variables that can influence the error literal (error cone
// of influence, those appear positively in error_coi). This information can
// then be used to eliminate such variables from the formulae and decrease the
// number of state variables.

struct aiger_info
{
    aiger* aig;

    // Aiger literals that are necessarily true. For any literal here, its
    // negation aiger_not( lit ) is necessarily false. This is used to
    // propagate constants and simplify the clausified formula. State variables
    // that are determined (i.e. always equal to true or false) don't need to
    // be computed in the transition formula (i.e. could be set as x' = true
    // or x' = false, respectively), or even better, can be removed from the
    // transition system completely, as long as we ensure that they don't
    // appear in the init, trans and error formulae.
    std::unordered_set< aiger_literal > true_literals;

    // The cone of influence of the error formula. Contains literals
    // corresponding to the latches that are necessary to decide the value
    // of the error literal. Any other latch x can have x' = false in the
    // transition formula and this won't compromise correctness. Even better,
    // any other latch can be simply deleted from the system completely (it
    // does not appear in the error formula by definition).
    std::unordered_set< aiger_literal > error_coi;
};

struct context
{
    aiger_info preprocessed_aiger;

    variable_range input_vars;
    variable_range state_vars;
    variable_range next_state_vars;
    variable_range and_vars;

    std::unordered_map< aiger_literal, variable > state_vars_table;
};

inline literal from_aiger_lit( const context& ctx, aiger_literal lit )
{
    const auto& aiger = ctx.preprocessed_aiger;

    const auto from_aiger_var = [ & ]( aiger_literal var )
    {
        // The aiger lib expects this to be a positive literal (i.e. a variable).
        assert( var % 2 == 0 );
        assert( var >= 2 ); // Not constants true/false

        if ( const auto *ptr = aiger_is_input( aiger.aig, var ); ptr )
            return ctx.input_vars.nth( static_cast< int >( ptr - aiger.aig->inputs ) );
        if ( const auto *ptr = aiger_is_latch( aiger.aig, var ); ptr )
            return assert( ctx.state_vars_table.contains( var ) ), ctx.state_vars_table.at( var );
        if ( const auto *ptr = aiger_is_and( aiger.aig, var ); ptr )
            return ctx.and_vars.nth( static_cast< int >( ptr - aiger.aig->ands ) );

        assert( false && "Unreachable code reached" );
        std::unreachable();
    };

    return literal
    {
        from_aiger_var( aiger_strip( lit ) ),
        aiger_sign( lit ) == 0
    };
}

std::expected< aiger_info, std::string > make_aiger_info( aiger& aig );
context make_context( variable_store& store, const aiger_info& info );
transition_system build_from_context( const context& ctx );

std::expected< transition_system, std::string > build_from_aiger( variable_store& store, aiger& aig );

}
