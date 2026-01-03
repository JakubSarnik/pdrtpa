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

cube sorted_cube_union( std::span< const literal > a, std::span< const literal > b )
{
    assert( std::ranges::is_sorted( a, cube_literal_lt ) );
    assert( std::ranges::is_sorted( b, cube_literal_lt ) );

    auto lits = std::vector( a.begin(), a.end() );
    lits.append_range( b );

    return cube{ std::move( lits ), is_sorted };
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
bool verifier::solve_obligation( const proof_obligation& po )
{
    assert( 0 <= po.level() && po.level() <= depth() );

    auto& cex = _cexes.get( po.handle() );
    const auto& s = cex.s_state_vars;
    const auto& t = cex.t_state_vars;

    // We need to first check if s /\ TF[ 0 ] /\ t' is satisfiable,
    // where TF[ 0 ] = id \/ T.

    // TODO: As long as we don't generalize states, a syntactic equivalence
    //       check suffices here.
    if ( intersects( s, t.literals() ) )
        return true;

    if ( has_concrete_edge( cex ) )
        return true;

    // We know from the previous that s /\ TF[ 0 ] /\ t' is unsatisfiable,
    // hence s does not reach t in <= 2^0 = 1 steps.
    if ( po.level() == 0 )
        return false;

    // TF[ 0 ]( X, X° ) /\ TF[ 0 ]( X°, X' ) /\ s /\ t' now reduces to
    // T( X, Y1, X° ) /\ T( X°, Y2, X' ) /\ s /\ t'.
    if ( po.level() == 1 )
        return has_path_of_length_two( cex );

    // TF[ k - 1 ]( X, X° ) /\ TF[ k - 1 ]( X°, X' ) /\ s /\ t'
    // TODO: Change this so has_middle_state sets cex.left and cex.right
    //       similarly to the previous code.
    auto u = has_middle_state( s.literals(), t.literals(), po.level() );

    while ( u.has_value() )
    {
        assert( !cex.left.has_value() );
        assert( !cex.right.has_value() );
        assert( is_state_cube( u->literals() ) );

        // TODO: See above about copying of u.
        auto left = proof_obligation{ _cexes.make( s, *u ), po.level() - 1 };
        auto right = proof_obligation{ _cexes.make( std::move( *u ), t ), po.level() - 1 };

        cex.left = left.handle();
        cex.right = right.handle();

        if ( solve_obligation( left ) && solve_obligation( right ) )
            return true;

        u = has_middle_state( s.literals(), t.literals(), po.level() );
    }

    // TODO: Generalize the blocked arrow here!
    block_arrow_at( s, t, po.level() );

    return false;
}

bool verifier::has_concrete_edge( cex_entry& cex )
{
    const auto& s = cex.s_state_vars.literals();
    const auto& t = cex.t_state_vars.literals();

    assert( is_state_cube( s ) );
    assert( is_state_cube( t ) );

    if ( _consecution_solver
            .query()
            .assume( _trans_activator )
            .assume( s )
            .assume( prime( t ) )
            .is_sat() )
    {
        assert( !cex.input_vars.has_value() );
        cex.input_vars = cube{ _consecution_solver.get_model( _system->input_vars() ), is_sorted };

        return true;
    }

    return false;
}

bool verifier::has_path_of_length_two( cex_entry& cex )
{
    const auto& s = cex.s_state_vars.literals();
    const auto& t = cex.t_state_vars.literals();

    assert( is_state_cube( s ) );
    assert( is_state_cube( t ) );

    if ( _consecution_solver
            .query()
            .assume( _left_trans_activator )
            .assume( _right_trans_activator )
            .assume( s )
            .assume( prime( t ) )
            .is_sat() )
    {
        auto middle_state = cube{ uncircle( _consecution_solver.get_model( _middle_state_vars ) ), is_sorted };

        assert( is_state_cube( middle_state.literals() ) );
        assert( !cex.left.has_value() );
        assert( !cex.right.has_value() );

        // TODO: Copying of the state cubes here is a bit ugly. Can't
        //       we store cubes in a pool?
        cex.left = _cexes.make( cex.s_state_vars, middle_state,
            cube{ _consecution_solver.get_model( _left_input_vars ), is_sorted } );
        cex.right = _cexes.make( std::move( middle_state ), cex.t_state_vars,
            cube{ _consecution_solver.get_model( _right_input_vars ), is_sorted } );

        return true;
    }

    return false;
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
        return cube{ uncircle( _consecution_solver.get_model( _middle_state_vars ) ), is_sorted };
    else
        return {};
}

void verifier::block_arrow_at( const cube& s, const cube& t, int level, int start_from /* = 1 */ )
{
    assert( 1 <= level && level <= depth() );
    assert( 1 <= start_from && start_from <= level );
    assert( is_state_cube( s.literals() ) );
    assert( is_state_cube( t.literals() ) );

    const auto c = sorted_cube_union( s.literals(), prime( t.literals() ) );

    for ( int d = start_from; d <= depth(); ++d )
    {
        auto& cubes = _trace_blocked_cubes[ d ];

        for ( std::size_t i = 0; i < cubes.size(); )
        {
            if ( c.subsumes( cubes[ i ] ) )
            {
                cubes[ i ] = cubes.back();
                cubes.pop_back();
            }
            else
                ++i;
        }
    }

    assert( level < _trace_blocked_cubes.size() );
    assert( level < _trace_activators.size() );

    _trace_blocked_cubes[ level ].emplace_back( c );

    const auto v = _trace_activators[ level ].var();

    _error_solver.assert_formula( c.negate().activate( v ) );
    _consecution_solver.assert_formula( sorted_cube_union( s.literals(), circle( t.literals() ) ).negate().activate( v ) );
    _consecution_solver.assert_formula( sorted_cube_union( prime( t.literals() ), circle( s.literals() ) ).negate().activate( v ) );
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
