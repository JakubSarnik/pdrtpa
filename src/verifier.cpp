#include "verifier.hpp"

auto verifier::run( const transition_system& system ) -> result_t
{
    _system = &system;
    initialize();

    return check();
}

void verifier::initialize()
{
    push_frame();

    _init_cube = _system->init().as_cube();

    // TODO: Set up solvers with the correctly activated formulae.
}

auto verifier::check() -> result_t
{
    // TODO
}
