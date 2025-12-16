#include "verifier.hpp"

auto verifier::run() -> result_t
{
    initialize();
    return check();
}

void verifier::initialize()
{
    push_frame();

    const auto next_state_error = _system->error().map( [ & ]( literal lit )
    {
        const auto [ type, pos ] = _system->get_var_info( lit.var() );

        if ( type == var_type::state )
            return _system->prime( lit );
        else
            return lit;
    } );

    _error_solver.assert_formula( _system->init() );
    _error_solver.assert_formula( next_state_error );

    const auto activated_trans = _system->trans().activate( _trans_activator.var() );
    const auto activated_left_trans = _left_trans.activate( _left_trans_activator.var() );
    const auto activated_right_trans = _right_trans.activate( _right_trans_activator.var() );

    // TODO: Do we want all this in the consecution solver? Consider splitting.
    _consecution_solver.assert_formula( activated_trans );
    _consecution_solver.assert_formula( activated_left_trans );
    _consecution_solver.assert_formula( activated_right_trans );
}

auto verifier::check() -> result_t
{
    // TODO
    return {};
}

// Check that there are no counterexamples of size 0, resp. 1
auto verifier::check_trivial_cases() -> result_t
{
    // TODO
    return {};
}
