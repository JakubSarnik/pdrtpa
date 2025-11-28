#pragma once

#include "logic.hpp"
#include "transition_system.hpp"
#include "aiger.h"
#include <unordered_set>
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
    // propagate constants and simplify the clausified formula. These don't
    // need to be computed in the transition formula (i.e. can be set as
    // x' = true or x' = false respectively), but they need to actually exist
    // in the formula because they can occur in the error formula.
    // Alternatively, they could be syntactically eliminated, or substituted
    // for a pair of values xtrue and xfalse that are kept true and false,
    // respectively, throughout the computation.
    // TODO: If there is any true state variable, make the first one xtrue.
    //       If there is any false state variable, make the first one xfalse.
    std::unordered_set< aiger_literal > true_literals;

    // The cone of influence of the error formula. Contains literals
    // corresponding to the latches that are necessary to decide the value
    // of the error literal. Any other latch x can have x' = false in the
    // transition formula and this won't compromise correctness. Even better,
    // any other latch can be deleted from the system completely (it does not
    // appear in the error formula by definition).
    std::unordered_set< aiger_literal > error_coi;
};

struct context
{
    aiger_info preprocessed_aiger;

    variable_range input_vars;
    variable_range state_vars;
    variable_range next_state_vars;
    variable_range and_vars;
};

std::expected< aiger_info, std::string > make_aiger_info( aiger& aig );
context make_context( variable_store& store, aiger_info& info );
transition_system build_from_context( context& ctx );

std::expected< transition_system, std::string > build_from_aiger( variable_store& store, aiger& aig );

}
