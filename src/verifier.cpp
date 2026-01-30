#include "verifier.hpp"
#include "logger.hpp"
#include <functional>
#include <queue>
#include <algorithm>

namespace
{

void sort_literals( std::span< literal > c )
{
    std::ranges::sort( c, cube_literal_lt );
}

// Simple = no repeating variables
[[maybe_unused]] bool is_sorted_and_simple( std::span< const literal > c )
{
    if ( !std::ranges::is_sorted( c, cube_literal_lt ) )
        return false;

    if ( c.empty() )
        return true;

    for ( auto i = 0uz; i < c.size() - 1; ++i )
    {
        if ( c[ i ].var() == c[ i + 1 ].var() )
            return false;
    }

    return true;
}

std::optional< literal > find_conflict_sorted( std::span< const literal > c, std::span< const literal > d )
{
    assert( is_sorted_and_simple( c ) );
    assert( is_sorted_and_simple( d ) );

    auto i = 0uz;
    auto j = 0uz;

    while ( i < c.size() && j < d.size() )
    {
        const auto x = c[ i ];
        const auto y = d[ j ];

        if ( x == !y )
            return x;

        if ( cube_literal_lt( x, !y ) )
            ++i;
        else // cube_literal_lt( !y, x ) holds
            ++j;
    }

    return {};
}

bool intersects_sorted( std::span< const literal > c, std::span< const literal > d )
{
    return !find_conflict_sorted( c, d ).has_value();
}

cube union_sorted( std::span< const literal > a, std::span< const literal > b )
{
    assert( std::ranges::is_sorted( a, cube_literal_lt ) );
    assert( std::ranges::is_sorted( b, cube_literal_lt ) );
    assert( a.empty() || b.empty() || cube_literal_lt( a.back(), b.front() ) );

    auto lits = std::vector( a.begin(), a.end() );
    lits.append_range( b );

    return cube{ std::move( lits ), is_sorted };
}

void insert_sorted( std::vector< literal >& lits, literal lit )
{
    assert( std::ranges::is_sorted( lits, cube_literal_lt ) );

    // TODO: Do a linear search here perhaps?

    const auto it = std::ranges::lower_bound( lits, lit, cube_literal_lt );

    if ( it != lits.end() && *it == lit )
        return;

    lits.insert( it, lit );
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

    assert( _trace_activators.size() == 1 );

    const auto activated_trans = _system->trans().activate( _trans_activator.var() );
    const auto activated_left_trans = _left_trans.activate( _trace_activators[ 0 ].var() );
    const auto activated_right_trans = _right_trans.activate( _trace_activators[ 0 ].var() );

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
            auto get_inputs = [ & ]( variable_range original_range )
            {
                return shift_literals( original_range, _system->input_vars(),
                    slv.get_model( original_range ) );
            };

            auto left_inputs = get_inputs( _left_input_vars );
            auto right_inputs = get_inputs( _right_input_vars );

            assert( is_input_cube( left_inputs ) );
            assert( is_input_cube( right_inputs ) );

            return std::vector
            {
                std::move( left_inputs ),
                std::move( right_inputs )
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

    // We need to first check if s /\ TF[ 0 ] /\ t' is satisfiable,
    // where TF[ 0 ] = id \/ T.

    if ( get_s( po ).literals() == get_t( po ).literals() )
        return true;

    if ( has_concrete_edge( po ) )
        return true;

    // We know from the previous that s /\ TF[ 0 ] /\ t' is unsatisfiable,
    // hence s does not reach t in <= 2^0 = 1 steps.
    if ( po.level() == 0 )
        return false;

    if ( po.level() == 1 )
    {
        // s /\ TF[ 0 ]( X, X° ) /\ TF[ 0 ]( X°, X' ) /\ t' now reduces to
        // s /\ T( X, Y1, X° ) /\ T( X°, Y2, X' ) /\ t'.

        if ( has_path_of_length_two( po ) )
            return true;
    }
    else
    {
        // s /\ TF[ k - 1 ]( X, X° ) /\ TF[ k - 1 ]( X°, X' ) /\ t'

        auto pair = split_obligation( po );

        while ( pair.has_value() )
        {
            const auto& [ left, right ] = *pair;

            // TODO: It might make sense to choose where to recurse first based
            //       on e.g. a coin toss or length of the cubes.
            if ( solve_obligation( left ) && solve_obligation( right ) )
                return true;

            pair = split_obligation( po );
        }
    }

    const auto [ c, d ] = generalize_blocked_arrow( get_s( po ), get_t( po ), po.level() );

    logger::log_line_debug( "{}: c = {}", po.level(), c.to_string() );
    logger::log_line_debug( "{}  d = {}", std::string( std::to_string( po.level() ).size(), ' '), d.to_string() );

    block_arrow_at( c, d, po.level() );

    return false;
}

bool verifier::has_concrete_edge( const proof_obligation& po )
{
    assert( is_state_cube( get_s( po ).literals() ) );
    assert( is_state_cube( get_t( po ).literals() ) );

    if ( _consecution_solver
            .query()
            .assume( _trans_activator )
            .assume( get_s( po ).literals() )
            .assume( prime( get_t( po ).literals() ) )
            .is_sat() )
    {
        assert( !get_inputs( po ).has_value() );
        _cexes.get( po.handle() ).input_vars = cube{ _consecution_solver.get_model( _system->input_vars() ), is_sorted };

        return true;
    }

    return false;
}

auto verifier::split_path( const proof_obligation& po )
    -> std::optional< std::pair< cex_handle, cex_handle > >
{
    assert( is_state_cube( get_s( po ).literals() ) );
    assert( is_state_cube( get_t( po ).literals() ) );
    assert( po.level() >= 1 && po.level() <= depth() ); // Level 0 cannot be split.

    if ( _consecution_solver
            .query()
            .assume( activators_from( po.level() - 1 ) )
            .assume( get_s( po ).literals() )
            .assume( prime( get_t( po ).literals() ) )
            .is_sat() )
    {
        auto u = cube{ uncircle( _consecution_solver.get_model( _middle_state_vars ) ), is_sorted };

        assert( is_state_cube( u.literals() ) );

        auto left_inputs = std::optional< cube >{};
        auto right_inputs = std::optional< cube >{};

        if ( po.level() == 1 )
        {
            auto get_inputs = [ & ]( variable_range original_range )
            {
                return cube{ shift_literals( original_range, _system->input_vars(),
                    _consecution_solver.get_model( original_range ) ), is_sorted };
            };

            left_inputs = get_inputs( _left_input_vars );
            right_inputs = get_inputs( _right_input_vars );

            assert( is_input_cube( left_inputs->literals() ) );
            assert( is_input_cube( right_inputs->literals() ) );
        }

        // TODO: Copying of the state cubes here is a bit ugly. Can't
        //       we store cubes in a pool?
        const auto left = _cexes.make( get_s( po ), u, std::move( left_inputs ) );
        const auto right = _cexes.make( std::move( u ), get_t( po ), std::move( right_inputs ) );

        _cexes.get( po.handle() ).left = left;
        _cexes.get( po.handle() ).right = right;

        return std::pair{ left, right };
    }

    return {};
}

bool verifier::has_path_of_length_two( const proof_obligation& po )
{
    assert( is_state_cube( get_s( po ).literals() ) );
    assert( is_state_cube( get_t( po ).literals() ) );
    assert( po.level() == 1 );

    return split_path( po ).has_value();
}

auto verifier::split_obligation( const proof_obligation& po )
    -> std::optional< std::pair< proof_obligation, proof_obligation > >
{
    assert( is_state_cube( get_s( po ).literals() ) );
    assert( is_state_cube( get_t( po ).literals() ) );
    assert( po.level() >= 2 && po.level() <= depth() ); // Levels 0 and 1 are checked separately

    return split_path( po ).transform( [ & ]( const std::pair< cex_handle, cex_handle >& split )
    {
        return std::pair
        {
            proof_obligation{ split.first, po.level() - 1 },
            proof_obligation{ split.second, po.level() - 1 }
        };
    } );
}

std::pair< cube, cube > verifier::generalize_blocked_arrow( const cube& s, const cube& t, int level )
{
    // We know that:
    // - s /\ TF[ 0 ] /\ t' is unsatisfiable, i.e.
    //   - s != t,
    //   - s /\ T( X, X' ) /\ t' is unsatisfiable, and
    // - s /\ TF[ k - 1 ]( X, X° ) /\ TF[ k - 1 ]( X°, X' ) /\ t' is
    //   unsatisfiable (and this was the last call, where k = level).
    // We need to produce subcubes c of s and d of t such that the previous
    // two formulae are still unsatisfiable when c is substituted for s
    // and d for t.

    assert( 1 <= level && level <= depth() );
    assert( is_state_cube( s.literals() ) );
    assert( is_state_cube( t.literals() ) );

    auto c = _consecution_solver.get_core( s.literals() );
    auto d = _consecution_solver.get_core_mapped( t.literals(), [ & ]( literal lit ){ return prime( lit ); } );

    // Cores ensure that
    //   c /\ TF[ k - 1 ]( X, X° ) /\ TF[ k - 1 ]( X°, X' ) /\ d'
    // is unsatisfiable. We now need to make sure that
    //   1. No state is in both c and d (i.e. c and d have empty intersection),
    //   2. No state in c can reach a state in d in one step.

    if ( intersects_sorted( c, d ) )
    {
        // Break the intersection by finding the first state variable that
        // occurs in s and t in different polarities (which must exist, since
        // otherwise we would have s = t) and appending the two separate
        // polarities to both c and d.

        const auto diff = find_conflict_sorted( s.literals(), t.literals() );
        assert( diff.has_value() );

        insert_sorted( c, *diff );
        insert_sorted( d, !*diff );
    }

    assert( !intersects_sorted( c, d ) );

    // Now we only need to ensure that c /\ T( X, Y, X' ) /\ d' is unsatisfiable.

    auto add_to_c = std::bernoulli_distribution{ 0.5 }; // NOLINT: 0.5 is a self-explanatory probability

    while ( _consecution_solver
                .query()
                .assume( _trans_activator )
                .assume( c )
                .assume( prime( d ) )
                .is_sat() )
    {
        const auto ss = _consecution_solver.get_model( _system->state_vars() );
        const auto tt = unprime( _consecution_solver.get_model( _system->next_state_vars() ) );

        const auto c_conflict = find_conflict_sorted( s.literals(), ss );
        const auto d_conflict = find_conflict_sorted( t.literals(), tt );

        if ( c_conflict.has_value() && d_conflict.has_value() )
        {
            if ( add_to_c( _random ) )
                c.push_back( *c_conflict );
            else
                d.push_back( *d_conflict );
        }
        else if ( c_conflict.has_value() )
        {
            c.push_back( *c_conflict );
        }
        else
        {
            assert( d_conflict.has_value() );
            d.push_back( *d_conflict );
        }
    }

    sort_literals( c );
    sort_literals( d );

    assert( !intersects_sorted( c, d ) );

    // The formula
    //   c /\ TF[ k - 1 ]( X, X° ) /\ TF[ k - 1 ]( X°, X' ) /\ d'
    // must still be unsatisfiable.

    assert( _consecution_solver
                .query()
                .assume( activators_from( level - 1 ) )
                .assume( c )
                .assume( prime( d ) )
                .is_unsat() );

    return { cube{ std::move( c ), is_sorted }, cube{ std::move( d ), is_sorted } };
}

void verifier::block_arrow_at( const cube& s, const cube& t, int level, int start_from /* = 1 */ )
{
    assert( 1 <= level && level <= depth() );
    assert( 1 <= start_from && start_from <= level );
    assert( is_state_cube( s.literals() ) );
    assert( is_state_cube( t.literals() ) );

    for ( int d = start_from; d <= level; ++d )
    {
        auto& arrows = _trace_blocked_arrows[ d ];

        for ( std::size_t i = 0; i < arrows.size(); )
        {
            const auto& [ other_s, other_t ] = arrows[ i ];

            assert( is_state_cube( other_s.literals() ) );
            assert( is_state_cube( other_t.literals() ) );

            if ( s.subsumes( other_s ) && t.subsumes( other_t ) )
            {
                arrows[ i ] = arrows.back();
                arrows.pop_back();
            }
            else
                ++i;
        }
    }

    assert( level < _trace_blocked_arrows.size() );
    assert( level < _trace_activators.size() );

    _trace_blocked_arrows[ level ].emplace_back( s, t );

    const auto v = _trace_activators[ level ].var();

    _error_solver.assert_formula( union_sorted( s.literals(), prime( t.literals() ) ).negate().activate( v ) );
    _consecution_solver.assert_formula( union_sorted( s.literals(), circle( t.literals() ) ).negate().activate( v ) );
    _consecution_solver.assert_formula( union_sorted( prime( t.literals() ), circle( s.literals() ) ).negate().activate( v ) );
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

// Returns true if the system has been proven safe by finding an invariant.
bool verifier::propagate()
{
    logger::log_line_debug( "Propagating to level {}", depth() );

    assert( depth() < _trace_blocked_arrows.size() );
    assert( _trace_blocked_arrows[ depth() ].empty() );

    // If
    //   c /\ TF[ k - 1 ]( X, X° ) /\ TF[ k - 1 ]( X°, X' ) /\ d'
    // is unsatisfiable, we can push (c, d') to TF[ k ].

    for ( int i = 1; i < depth(); ++i )
    {
        // The copy is done since the _trace_blocked_arrows[ i ] will be changed
        // during the forthcoming iteration.
        const auto arrows = _trace_blocked_arrows[ i ];

        for ( const auto& [ c, d ] : arrows )
        {
            if ( _consecution_solver
                    .query()
                    .assume( activators_from( i ) )
                    .assume( c.literals() )
                    .assume( prime( d.literals() ) )
                    .is_unsat() )
            {
                // TODO: Further generalization from core?
                //       (E.g. as in generalize_from_core in PDR).
                block_arrow_at( c, d, i + 1, i );
            }
        }

        if ( _trace_blocked_arrows[ i ].empty() )
            return true;
    }

    log_trace_content();

    return false;
}

void verifier::log_trace_content() const
{
    auto line = std::format( "{}:", depth() );

    for ( int i = 1; i <= depth(); ++i )
        line += std::format( " {}", _trace_blocked_arrows[ i ].size() );

    logger::log_line_loud( "{}", line );
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

bool verifier::is_input_cube( std::span< const literal > literals ) const
{
    const auto is_input_var = [ & ]( variable var )
    {
        const auto [ type, _ ] = _system->get_var_info( var );
        return type == var_type::input;
    };

    return std::ranges::all_of( literals, [ & ]( literal lit ){ return is_input_var( lit.var() ); } );
}
