#include "verifier.hpp"
#include "logger.hpp"
#include <functional>
#include <queue>

namespace
{

// TODO: Consider adding a more efficient implementation for two cubes.
bool intersects( const cube& c, std::span< const literal > d )
{
    for ( const auto lit : d )
        if ( c.contains( !lit ) )
            return false;

    return true;
}

}

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
            if ( solve_obligation( { *cex, depth() } ) )
                return build_counterexample( *cex );
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
        return _cexes.make( cube{ _error_solver.get_model( _system->state_vars() ), is_sorted },
                            cube{ unprime( _error_solver.get_model( _system->next_state_vars() ) ), is_sorted },
                            cube{ _error_solver.get_model( _system->input_vars() ), is_sorted } );
    }

    return {};
}

// Returns true if a counterexample is found. Main loop then knows that
// the counterexample is rooted in starting_po.
bool verifier::solve_obligation( const proof_obligation& starting_po )
{
    assert( 0 <= starting_po.level() && starting_po.level() <= depth() );

    // TODO: Do we want a priority queue here, or does a recursive scheme
    //       suffice/work better?

    auto min_queue = std::priority_queue< proof_obligation,
        std::vector< proof_obligation >, std::greater<> >{};

    min_queue.push( starting_po );

    while ( !min_queue.empty() )
    {
        auto po = min_queue.top();
        min_queue.pop();

        auto& cex = _cexes.get( po.handle() );
        const auto& s = cex.s_state_vars;
        const auto& t = cex.t_state_vars;

        // We need to first check if s /\ TF[ 0 ] /\ t' is satisfiable,
        // where TF[ 0 ] = id \/ T.

        if ( intersects( s, t.literals() ) )
            return true;

        // TODO: Consider decomposing this even further, has_* should also set inputs, left and right!
        //       That way, we could get rid of two_edges and similar stuff.
        if ( auto ins = has_edge( s.literals(), t.literals() ); ins.has_value() )
        {
            assert( !cex.input_vars.has_value() );
            cex.input_vars = std::move( *ins );

            return true;
        }

        // We know from the previous that s /\ TF[ 0 ] /\ t' is unsatisfiable,
        // hence s does not reach t in <= 2^0 = 1 steps.
        if ( po.level() == 0 )
            continue;

        if ( po.level() == 1 )
        {
            // TF[ 0 ]( X, X° ) /\ TF[ 0 ]( X°, X' ) /\ s /\ t' reduces to
            // T( X, Y1, X° ) /\ T( X°, Y2, X' ) /\ s /\ t'.

            if ( auto path = has_path_of_length_two( s.literals(), t.literals() ); path.has_value() )
            {
                assert( !cex.left.has_value() );
                assert( !cex.right.has_value() );

                // TODO: Copying of the middle state here is a bit ugly. Can't
                //       we store cubes in a pool?
                cex.left = _cexes.make( s, path->middle_state, std::move( path->left_input ) );
                cex.right = _cexes.make( std::move( path->middle_state ), t, std::move( path->right_input ) );

                return true;
            }
        }
        else
        {
            // TODO: Is already blocked?
            // TF[ k - 1 ]( X, X° ) /\ TF[ k - 1 ]( X°, X' ) /\ s /\ t'

            if ( auto u = has_middle_state( s.literals(), t.literals(), po.level() ); u.has_value() )
            {
                // TODO: Middle state u found
            }
            else
            {
                // TODO: No middle state found
            }
        }
    }

    return false;
}

std::optional< cube > verifier::has_edge( std::span< const literal > s, std::span< const literal > t )
{
    assert( is_state_cube( s ) );
    assert( is_state_cube( t ) );

    if ( _consecution_solver
            .query()
            .assume( _trans_activator )
            .assume( s )
            .assume( prime( t ) )
            .is_sat() )
        return cube{ _consecution_solver.get_model( _system->input_vars() ), is_sorted };
    else
        return {};
}

auto verifier::has_path_of_length_two( std::span< const literal > s, std::span< const literal > t )
    -> std::optional< two_edges >
{
    assert( is_state_cube( s ) );
    assert( is_state_cube( t ) );

    if ( _consecution_solver
            .query()
            .assume( _left_trans_activator )
            .assume( _right_trans_activator )
            .assume( s )
            .assume( prime( t ) )
            .is_sat() )
        return two_edges
        {
            .left_input = cube{ _consecution_solver.get_model( _left_input_vars ), is_sorted },
            .middle_state = cube{ uncircle( _consecution_solver.get_model( _middle_state_vars ) ), is_sorted },
            .right_input = cube{ _consecution_solver.get_model( _right_input_vars ), is_sorted }
        };
    else
        return {};
}

std::optional< cube > verifier::has_middle_state( std::span< const literal > s, std::span< const literal > t,
    int level )
{
    assert( is_state_cube( s ) );
    assert( is_state_cube( t ) );
    assert( level >= 2 && level <= depth() ); // Levels 0 and 1 are checked separately

    if ( _consecution_solver
            .query()
            .assume( activators_from( level - 1 ) )
            .assume( s )
            .assume( prime( t ) )
            .is_sat() )
        return cube{ unprime( _consecution_solver.get_model( _middle_state_vars ) ), is_sorted };
    else
        return {};
}

std::vector< std::vector< literal > > verifier::build_counterexample( cex_handle root )
{
    auto inputs = std::vector< std::vector< literal > >{};

    std::function< void( std::optional< cex_handle > ) > visit = [ & ]( std::optional< cex_handle > handle )
    {
        if ( !handle.has_value() )
            return;

        const auto cex = _cexes.get( *handle );

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

// Returns true if cube contains only state variables. Used for assertions
// only.
bool verifier::is_state_cube( std::span< const literal > literals ) const
{
    const auto is_state_var = [ & ]( variable var )
    {
        const auto [ type, _ ] = _system->get_var_info( var );
        return type == var_type::state;
    };

    return std::ranges::all_of( literals, [ & ]( literal lit ){ return is_state_var( lit.var() ); } );
}
