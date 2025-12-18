#include "verifier.hpp"
#include "logger.hpp"
#include <functional>

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
    if ( auto res = check_trivial_cases(); res.has_value() )
        return res;

    logger::log_line_debug( "Beginning main loop" );

    push_frame();

    while ( true )
    {
        if ( const auto cex = get_error_cex(); cex.has_value() )
        {
            if ( const auto trace = solve_obligation( { *cex, depth() } ); trace.has_value() )
                return trace;
        }
        else
        {
            push_frame();

            if ( propagate() )
                return {};
        }

        _cexes.clear();
    }
}

// Check that there are no counterexamples of size 0, resp. 1
auto verifier::check_trivial_cases() -> result_t
{
    logger::log_line_debug("Checking I(X) ∧ E(X, Y)");

    {
        auto slv = solver{};

        slv.assert_formula( _system->init() );
        slv.assert_formula( _system->error() );

        if ( slv.query().is_sat() )
        {
            return std::vector< std::vector< literal > >{ slv.get_model( _system->input_vars() ) };
        }
    }

    logger::log_line_debug("Checking I(X) ∧ T(X, Y₁, X') ∧ E(X', Y₂)");

    {
        // E(X', Y2)
        const auto shifted_error = _system->error().map( [ & ]( literal lit )
        {
            const auto [ type, pos ] = _system->get_var_info( lit.var() );

            switch ( type )
            {
                case var_type::state:
                    return _system->prime( lit );
                case var_type::input:
                    return lit.substitute( _right_input_vars.nth( pos ) );
                default:
                    return lit;
            }
        } );

        auto slv = solver{};

        slv.assert_formula( _system->init() );
        slv.assert_formula( _system->trans() );
        slv.assert_formula( shifted_error );

        if ( slv.query().is_sat() )
        {
            return std::vector
            {
                slv.get_model( _left_input_vars ),
                slv.get_model( _right_input_vars )
            };
        }
    }

    return {};
}

// Make a new proof obligation representing a model of
// I(X) /\ TF[i](X, X') /\ E(X', Y), where i >= 1
std::optional< cex_handle > verifier::get_error_cex()
{
    assert( depth() >= 1 );

    if ( _error_solver.query()
        .assume( activators_from( depth() ) )
        .is_sat() )
    {
        return _cexes.make( cube{ _error_solver.get_model( _system->state_vars() ) },
                               cube{ _error_solver.get_model( _system->input_vars() ) } );
    }

    return {};
}

auto verifier::solve_obligation( const proof_obligation& starting_po ) -> result_t
{
    // TODO
}

std::vector< std::vector< literal > > verifier::build_counterexample( cex_handle root )
{
    auto inputs = std::vector< std::vector< literal > >{};

    std::function< void( cex_handle ) > visit = [ & ]( cex_handle handle )
    {
        if ( !_cexes.is_valid( handle ) )
            return;

        const auto cex = _cexes.get( handle );

        visit( cex.left );
        visit( cex.right );

        if ( cex.input_vars.has_value() )
        {
            auto row = std::vector< literal >{};
            row.reserve( _system->input_vars().size() );

            // If a variable doesn't appear in any literal, its value is not
            // important, so we might as well just make it false.
            for ( const auto in : _system->input_vars() )
                row.push_back( cex.input_vars->find( in ).value_or( literal{ in, false } ) );

            inputs.emplace_back( std::move( row ) );
        }
    };

    visit( root );

    return inputs;
}

bool verifier::propagate()
{
    // TODO
}
