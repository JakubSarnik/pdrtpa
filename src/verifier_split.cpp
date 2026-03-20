#include "verifier_split.hpp"
#include "logger.hpp"
#include <functional>
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

    const auto it = std::ranges::lower_bound( lits, lit, cube_literal_lt );

    if ( it != lits.end() && *it == lit )
        return;

    lits.insert( it, lit );
}

}

auto verifier_split::run() -> result_t
{
    initialize();
    return check();
}

void verifier_split::initialize()
{
    push_frame();

    const auto next_state_error = _system->error().map( [ & ]( literal lit )
    {
        const auto [ type, pos ] = _system->get_var_info( lit.var() );

        if ( type == var_type::state )
            return prime( lit );
        else
            return lit;
    } );

    _equality_error_solver.assert_formula( _system->init() );
    _equality_error_solver.assert_formula( next_state_error );

    _less_than_error_solver.assert_formula( _system->init() );
    _less_than_error_solver.assert_formula( next_state_error );

    _one_step_solver.assert_formula( _system->trans() );

    _two_steps_solver.assert_formula( _left_trans );
    _two_steps_solver.assert_formula( _right_trans );
}

auto verifier_split::check() -> result_t
{
    if ( auto res = check_trivial_cases(); res.has_value() )
        return res;

    logger::log_line_debug( "Beginning main loop" );

    push_frame();

    while ( true )
    {
        auto cex = std::optional< cex_handle >{};

        while ( ( cex = get_equality_error_cex() ) )
            if ( solve_equality_obligation( { *cex, depth() } ) )
                return build_counterexample( *cex );

        while ( ( cex = get_less_than_error_cex() ) )
            if ( solve_less_than_obligation( { *cex, depth() } ) )
                return build_counterexample( *cex );

        push_frame();

        const auto propagated_equality_frame = propagate_equality();
        const auto propagated_less_than_frame = propagate_less_than();

        if ( propagated_equality_frame && propagated_less_than_frame )
            return {};

        _cexes.clear();
    }
}

// Check that there are no counterexamples of size 0, resp. 1
auto verifier_split::check_trivial_cases() -> result_t
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
                    return prime( lit );
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
// I(X) /\ TF=[i](X, X') /\ E(X', Y), where i >= 1
std::optional< cex_handle > verifier_split::get_equality_error_cex()
{
    assert( depth() >= 1 );

    if ( _equality_error_solver.query()
        .assume( equality_activator_at( depth() ) )
        .is_sat() )
    {
        return _cexes.make( cube{ _equality_error_solver.get_model( _system->state_vars() ), is_sorted },
                            cube{ unprime( _equality_error_solver.get_model( _system->next_state_vars() ) ), is_sorted },
                            cube{ _equality_error_solver.get_model( _system->input_vars() ), is_sorted } );
    }

    return {};
}

// Make a new proof obligation representing a model of
// I(X) /\ TF<[i](X, X') /\ E(X', Y), where i >= 1
std::optional< cex_handle > verifier_split::get_less_than_error_cex()
{
    assert( depth() >= 1 );

    if ( _less_than_error_solver.query()
        .assume( less_than_activators_from( depth() ) )
        .is_sat() )
    {
        return _cexes.make( cube{ _less_than_error_solver.get_model( _system->state_vars() ), is_sorted },
                            cube{ unprime( _less_than_error_solver.get_model( _system->next_state_vars() ) ), is_sorted },
                            cube{ _less_than_error_solver.get_model( _system->input_vars() ), is_sorted } );
    }

    return {};
}

// Returns true if a counterexample is found. Main loop then knows that
// the counterexample is rooted in starting_po.
bool verifier_split::solve_equality_obligation( const proof_obligation& po )
{
    assert( 0 <= po.level() && po.level() <= depth() );

    // We need to first check if s /\ TF=[ 0 ] /\ t' is satisfiable,
    // where TF=[ 0 ] = T.

    // TODO: Do we have to check this for all cases, or just when level = 0?
    if ( has_concrete_edge( po ) )
        return true;

    // We know from the previous that s /\ TF=[ 0 ] /\ t' is unsatisfiable,
    // hence s does not reach t in = 2^0 = 1 step.
    if ( po.level() == 0 )
        return false;

    if ( po.level() == 1 )
    {
        // s /\ TF=[ 0 ]( X, X° ) /\ TF=[ 0 ]( X°, X' ) /\ t' now reduces to
        // s /\ T( X, Y1, X° ) /\ T( X°, Y2, X' ) /\ t'.

        if ( has_path_of_length_two( po ) )
            return true;
    }
    else
    {
        // s /\ TF=[ k - 1 ]( X, X° ) /\ TF=[ k - 1 ]( X°, X' ) /\ t'

        auto pair = split_equality_obligation( po );

        while ( pair.has_value() )
        {
            const auto& [ left, right ] = *pair;

            if ( solve_equality_obligation( left ) && solve_equality_obligation( right ) )
                return true;

            pair = split_equality_obligation( po );
        }
    }

    auto [ c_vec, d_vec, block_at ] =
        generalize_blocked_equality_arrow( get_s( po ).literals(), get_t( po ).literals(), po.level() );

    auto c = cube{ std::move( c_vec ), is_sorted };
    auto d = cube{ std::move( d_vec ), is_sorted };

    logger::log_line_debug( "={}: c = {}", po.level(), c.to_string() );
    logger::log_line_debug( " {}  d = {}", std::string( std::to_string( po.level() ).size(), ' '), d.to_string() );

    for ( auto i = po.level(); i <= block_at; ++i )
        block_equality_arrow_at( c, d, i );

    return false;
}

// Same as above
bool verifier_split::solve_less_than_obligation( const proof_obligation& po )
{
    assert( 0 <= po.level() && po.level() <= depth() );

    // We need to first check if s /\ TF<[ 0 ] /\ t' is satisfiable,
    // where TF<[ 0 ] = id.

    // TODO: Do we have to check this for all cases, or just when level = 0?
    if ( get_s( po ).literals() == get_t( po ).literals() )
        return true;

    // We know from the previous that s /\ TF<[ 0 ] /\ t' is unsatisfiable,
    // hence s does not reach t in < 2^0 = 1 step.
    if ( po.level() == 0 )
        return false;

    if ( po.level() == 1 )
    {
        // s /\ TF=[ 0 ]( X, X° ) /\ TF<[ 0 ]( X°, X' ) /\ t' now reduces to
        // s /\ T( X, Y, X' ) /\ t'.

        if ( has_concrete_edge( po ) )
            return true;
    }
    else
    {
        // s /\ TF=[ k - 1 ]( X, X° ) /\ TF<[ k - 1 ]( X°, X' ) /\ t'

        auto pair = split_less_than_obligation( po );

        while ( pair.has_value() )
        {
            const auto& [ left, right ] = *pair;

            if ( solve_equality_obligation( left ) && solve_less_than_obligation( right ) )
                return true;

            pair = split_less_than_obligation( po );
        }
    }

    auto [ c_vec, d_vec, block_at ] =
        generalize_blocked_less_than_arrow( get_s( po ).literals(), get_t( po ).literals(), po.level() );

    auto c = cube{ std::move( c_vec ), is_sorted };
    auto d = cube{ std::move( d_vec ), is_sorted };

    logger::log_line_debug( "<{}: c = {}", po.level(), c.to_string() );
    logger::log_line_debug( " {}  d = {}", std::string( std::to_string( po.level() ).size(), ' '), d.to_string() );

    block_less_than_arrow_at( std::move( c ), std::move( d ), block_at );

    return false;
}

// Is
//   c /\ T( X, Y, X' ) /\ d'
// satisfiable?
bool verifier_split::has_edge( std::span< const literal > c, std::span< const literal > d )
{
    assert( is_state_cube( c ) );
    assert( is_state_cube( d ) );

    return _one_step_solver
           .query()
           .assume( c )
           .assume( prime( d ) )
           .is_sat();
}

// Is
//   c /\ TF=[ level - 1 ]( X, X° ) /\ TF=[ level - 1 ]( X°, X' ) /\ d'
// satisfiable?
bool verifier_split::has_equality_middle_point( std::span< const literal > c, std::span< const literal > d, int level )
{
    assert( is_state_cube( c ) );
    assert( is_state_cube( d ) );
    assert( level >= 1 && level <= depth() + 1 );

    auto builder = get_equality_solver_for( level ).query();

    builder.assume( c )
           .assume( prime( d ) );

    if ( level > 1 )
        builder.assume( equality_activator_at( level - 1 ) );

    return builder.is_sat();
}

// Is
//   c /\ TF=[ level - 1 ]( X, X° ) /\ TF<[ level - 1 ]( X°, X' ) /\ d'
// satisfiable?
bool verifier_split::has_less_than_middle_point( std::span< const literal > c, std::span< const literal > d, int level )
{
    assert( is_state_cube( c ) );
    assert( is_state_cube( d ) );
    assert( level >= 1 && level <= depth() + 1 );

    auto builder = get_less_than_solver_for( level ).query();

    builder.assume( c )
           .assume( prime( d ) );

    if ( level > 1 )
    {
        builder.assume( equality_activator_at( level - 1 ) );
        builder.assume( less_than_activators_from( level - 1 ) );
    }

    return builder.is_sat();
}

bool verifier_split::has_concrete_edge( const proof_obligation& po )
{
    assert( is_state_cube( get_s( po ).literals() ) );
    assert( is_state_cube( get_t( po ).literals() ) );

    if ( has_edge( get_s( po ).literals(), get_t( po ).literals() ) )
    {
        assert( !get_inputs( po ).has_value() );
        _cexes.get( po.handle() ).input_vars = cube{ _one_step_solver.get_model( _system->input_vars() ), is_sorted };

        return true;
    }

    return false;
}

std::optional< std::pair< cex_handle, cex_handle > > verifier_split::split_equality_path( const proof_obligation& po )
{
    assert( is_state_cube( get_s( po ).literals() ) );
    assert( is_state_cube( get_t( po ).literals() ) );
    assert( po.level() >= 1 && po.level() <= depth() ); // Level 0 cannot be split.

    if ( has_equality_middle_point( get_s( po ).literals(), get_t( po ).literals(), po.level() ) )
    {
        auto u = cube{ uncircle( get_equality_solver_for( po.level() ).get_model( _middle_state_vars ) ), is_sorted };

        assert( is_state_cube( u.literals() ) );

        auto left_inputs = std::optional< cube >{};
        auto right_inputs = std::optional< cube >{};

        if ( po.level() == 1 )
        {
            auto get_inputs = [ & ]( variable_range original_range )
            {
                return cube{ shift_literals( original_range, _system->input_vars(),
                    get_equality_solver_for( po.level() ).get_model( original_range ) ), is_sorted };
            };

            left_inputs = get_inputs( _left_input_vars );
            right_inputs = get_inputs( _right_input_vars );

            assert( is_input_cube( left_inputs->literals() ) );
            assert( is_input_cube( right_inputs->literals() ) );
        }

        // Cubes are copied here, but we tried a version with cubes stored in
        // a pool and benchmarked runtimes were basically identical at the cost
        // of more convoluted code.

        const auto left = _cexes.make( get_s( po ), u, std::move( left_inputs ) );
        const auto right = _cexes.make( std::move( u ), get_t( po ), std::move( right_inputs ) );

        _cexes.get( po.handle() ).left = left;
        _cexes.get( po.handle() ).right = right;

        return std::pair{ left, right };
    }

    return {};
}

std::optional< std::pair< cex_handle, cex_handle > > verifier_split::split_less_than_path( const proof_obligation& po )
{
    assert( is_state_cube( get_s( po ).literals() ) );
    assert( is_state_cube( get_t( po ).literals() ) );
    assert( po.level() >= 2 && po.level() <= depth() ); // Levels 0 and 1 cannot be split.

    if ( has_less_than_middle_point( get_s( po ).literals(), get_t( po ).literals(), po.level() ) )
    {
        auto u = cube{ uncircle( get_less_than_solver_for( po.level() ).get_model( _middle_state_vars ) ), is_sorted };

        assert( is_state_cube( u.literals() ) );

        const auto left = _cexes.make( get_s( po ), u );
        const auto right = _cexes.make( std::move( u ), get_t( po ) );

        _cexes.get( po.handle() ).left = left;
        _cexes.get( po.handle() ).right = right;

        return std::pair{ left, right };
    }

    return {};
}

bool verifier_split::has_path_of_length_two( const proof_obligation& po )
{
    assert( is_state_cube( get_s( po ).literals() ) );
    assert( is_state_cube( get_t( po ).literals() ) );
    assert( po.level() == 1 );

    return split_equality_path( po ).has_value();
}

std::optional< std::pair< proof_obligation, proof_obligation > > verifier_split::split_equality_obligation( const proof_obligation& po )
{
    assert( is_state_cube( get_s( po ).literals() ) );
    assert( is_state_cube( get_t( po ).literals() ) );
    assert( po.level() >= 2 && po.level() <= depth() ); // Levels 0 and 1 are checked separately

    return split_equality_path( po ).transform( [ & ]( const std::pair< cex_handle, cex_handle >& split )
    {
        return std::pair
        {
            proof_obligation{ split.first, po.level() - 1 },
            proof_obligation{ split.second, po.level() - 1 }
        };
    } );
}

std::optional< std::pair< proof_obligation, proof_obligation > > verifier_split::split_less_than_obligation( const proof_obligation& po )
{
    assert( is_state_cube( get_s( po ).literals() ) );
    assert( is_state_cube( get_t( po ).literals() ) );
    assert( po.level() >= 2 && po.level() <= depth() ); // Levels 0 and 1 are checked separately

    return split_less_than_path( po ).transform( [ & ]( const std::pair< cex_handle, cex_handle >& split )
    {
        return std::pair
        {
            proof_obligation{ split.first, po.level() - 1 },
            proof_obligation{ split.second, po.level() - 1 }
        };
    } );
}

auto verifier_split::generalize_blocked_equality_arrow( std::span< const literal > s, std::span< const literal > t, int level )
        -> std::tuple< std::vector< literal >, std::vector< literal >, int >
{
    assert( 1 <= level && level <= depth() );
    assert( is_state_cube( s ) );
    assert( is_state_cube( t ) );
    // CONTRACT: The previous SAT call was has_equality_middle_point and it
    //           returned false.

    auto [ c, d ] = equality_generalize_from_core( s, t, level );

    auto original_c = c;
    auto original_d = d;

    std::ranges::shuffle( original_c, _random );
    std::ranges::shuffle( original_d, _random );

    const auto try_drop = [ & ]( std::vector< literal >& drop_from, literal lit )
    {
        if ( const auto erased = std::erase( drop_from, lit ); erased == 0 )
            return;

        if ( has_equality_middle_point( c, d, level ) )
            insert_sorted( drop_from, lit );
        else
            std::tie( c, d  ) = equality_generalize_from_core( c, d, level );
    };

    for ( const auto lit : original_c )
        try_drop( c, lit );

    for ( const auto lit : original_d )
        try_drop( d, lit );

    auto block_at = level;

    while ( block_at <= depth() )
    {
        if ( !has_equality_middle_point( c, d, block_at + 1 ) )
        {
            std::tie( c, d ) = equality_generalize_from_core( c, d, block_at + 1 );
            ++block_at;
        }
        else
            break;
    }

    return { std::move( c ), std::move( d ), block_at };
}

auto verifier_split::equality_generalize_from_core( std::span< const literal > s, std::span< const literal > t, int level )
    -> std::tuple< std::vector< literal >, std::vector< literal > >
{
    // We know that:
    // - s /\ TF=[ 0 ] /\ t' is unsatisfiable, i.e.
    //     s /\ T( X, Y, X' ) /\ t'
    //   is unsatisfiable, and
    // - s /\ TF=[ k - 1 ]( X, X° ) /\ TF=[ k - 1 ]( X°, X' ) /\ t' is
    //   unsatisfiable (and this was the last call, where k = level).
    // We need to produce subcubes c of s and d of t such that the previous
    // two formulae are still unsatisfiable when c is substituted for s
    // and d for t.

    assert( 1 <= level && level <= depth() + 1 );
    assert( is_state_cube( s ) );
    assert( is_state_cube( t ) );
    // CONTRACT: The previous SAT call was has_equality_middle_point and it
    //           returned false.

    auto c = get_equality_solver_for( level ).get_core( s );
    auto d = get_equality_solver_for( level ).get_core_mapped( t, [ & ]( literal lit ){ return prime( lit ); } );

    // Cores ensure that
    //   c /\ TF[ k - 1 ]( X, X° ) /\ TF[ k - 1 ]( X°, X' ) /\ d'
    // is unsatisfiable.

    assert( !has_equality_middle_point( c, d, level ) );

    return { std::move( c ), std::move( d ) };
}

auto verifier_split::generalize_blocked_less_than_arrow( std::span< const literal > s, std::span< const literal > t, int level )
    -> std::tuple< std::vector< literal >, std::vector< literal >, int >
{
    assert( 1 <= level && level <= depth() );
    assert( is_state_cube( s ) );
    assert( is_state_cube( t ) );
    // CONTRACT: The previous SAT call was has_less_than_middle_point and it
    //           returned false.

    auto [ c, d, block_at ] = less_than_generalize_from_core( s, t, level );

    auto original_c = c;
    auto original_d = d;

    std::ranges::shuffle( original_c, _random );
    std::ranges::shuffle( original_d, _random );

    const auto try_drop = [ & ]( std::vector< literal >& drop_from, literal lit )
    {
        if ( const auto erased = std::erase( drop_from, lit ); erased == 0 )
            return;

        if ( intersects_sorted( c, d ) || has_less_than_middle_point( c, d, level ) )
            insert_sorted( drop_from, lit );
        else
            std::tie( c, d, block_at ) = less_than_generalize_from_core( c, d, level );
    };

    for ( const auto lit : original_c )
        try_drop( c, lit );

    for ( const auto lit : original_d )
        try_drop( d, lit );

    // TODO: Try to raise the level.

    return { std::move( c ), std::move( d ), block_at };
}

auto verifier_split::less_than_generalize_from_core( std::span< const literal > s, std::span< const literal > t, int level )
    -> std::tuple< std::vector< literal >, std::vector< literal >, int >
{
    // We know that:
    // - s /\ TF<[ 0 ] /\ t' is unsatisfiable, i.e. s != t, and
    // - s /\ TF=[ k - 1 ]( X, X° ) /\ TF<[ k - 1 ]( X°, X' ) /\ t' is
    //   unsatisfiable (and this was the last call, where k = level).
    // We need to produce subcubes c of s and d of t such that the previous
    // two formulae are still unsatisfiable when c is substituted for s
    // and d for t.

    assert( 1 <= level && level <= depth() );
    assert( is_state_cube( s ) );
    assert( is_state_cube( t ) );
    // CONTRACT: The previous SAT call was has_less_than_middle_point and it
    //           returned false.

    auto c = get_less_than_solver_for( level ).get_core( s );
    auto d = get_less_than_solver_for( level ).get_core_mapped( t, [ & ]( literal lit ){ return prime( lit ); } );

    // Cores ensure that
    //   c /\ TF[ k - 1 ]( X, X° ) /\ TF[ k - 1 ]( X°, X' ) /\ d'
    // is unsatisfiable. We only need to ensure that c and d have empty
    // intersection.

    if ( intersects_sorted( c, d ) )
    {
        // We need to break the intersection by making sure that there is a
        // literal that occurs in different polarities in c and d (a conflict
        // literal). If the original s has an empty intersection with d, there
        // is a conflict literal which we can add to c to restore the conflict
        // with d. The case of non-intersecting c and t is symmetric. Finally,
        // it might be the case that neither s and d nor c and t are in
        // conflict. However, we know that the original cubes s and t
        // definitely are in conflict, otherwise they wouldn't be blocked (and
        // therefore generalized), since (s, t) would contain an identity
        // arrow.

        if ( const auto diff1 = find_conflict_sorted( s, d ); diff1.has_value() )
        {
            insert_sorted( c, *diff1 );
        }
        else if ( const auto diff2 = find_conflict_sorted( c, t ); diff2.has_value() )
        {
            insert_sorted( d, !*diff2 );
        }
        else
        {
            const auto diff3 = find_conflict_sorted( s, t );
            assert( diff3.has_value() );

            insert_sorted( c, *diff3 );
            insert_sorted( d, !*diff3 );
        }
    }

    assert( !intersects_sorted( c, d ) );

    // The formula
    //   c /\ TF[ k - 1 ]( X, X° ) /\ TF[ k - 1 ]( X°, X' ) /\ d'
    // must still be unsatisfiable.

    assert( !has_less_than_middle_point( c, d, level ) );

    // TODO: Remove the level parameter from the function

    return { std::move( c ), std::move( d ), level };
}

void verifier_split::block_equality_arrow_at( cube s, cube t, int level )
{
    assert( 1 <= level && level <= depth() + 1 );
    assert( is_state_cube( s.literals() ) );
    assert( is_state_cube( t.literals() ) );

    const auto k = std::min( level, depth() );

    // We want to block s /\ t' as a model of
    //   TF=[ k ]( X, X' ), TF=[ k ]( X, X° ) and TF=[ k ]( X°, X' ).
    // That is, we need to add s /\ t' to the equality frame TF=[ k ] and
    // assert
    //   - ~(s /\ t') in the equality error solver,
    //   - ~(s /\ t°) and ~(s° /\ t') in the equality consecution solver,
    //   - ~(s /\ t°) in the less-than consecution solver,
    // always activated by the equality activator at level k.

    auto& arrows = _equality_trace_blocked_arrows[ k ];

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

    assert( k < _equality_trace_blocked_arrows.size() );
    assert( k < _equality_trace_activators.size() );

    const auto v = _equality_trace_activators[ k ].var();
    const auto circled_left = union_sorted( s.literals(), circle( t.literals() ) ).negate().activate( v );

    _equality_error_solver.assert_formula( union_sorted( s.literals(), prime( t.literals() ) ).negate().activate( v ) );
    _equality_consecution_solver.assert_formula( circled_left );
    _equality_consecution_solver.assert_formula( union_sorted( prime( t.literals() ), circle( s.literals() ) ).negate().activate( v ) );

    _less_than_consecution_solver.assert_formula( circled_left );

    _equality_trace_blocked_arrows[ k ].emplace_back( std::move( s ), std::move( t ) );
}

void verifier_split::block_less_than_arrow_at( cube s, cube t, int level, int start_from /* = 1 */ )
{
    assert( 1 <= level && level <= depth() );
    assert( 1 <= start_from && start_from <= level );
    assert( is_state_cube( s.literals() ) );
    assert( is_state_cube( t.literals() ) );

    // We want to block s /\ t' as a model of
    //   TF<[ k ]( X, X' ) (error) and TF<[ k ]( X°, X' ) (consecution).
    // That is, we need to add s /\ t' to the less-than frame TF<[ k ] and
    // assert
    //   - ~(s /\ t') in the less-than error solver, and
    //   - ~(s° /\ t') in the less-than consecution solver
    // always activated by the less-than activator at level k.

    for ( int d = start_from; d <= level; ++d )
    {
        auto& arrows = _less_than_trace_blocked_arrows[ d ];

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

    assert( level < _less_than_trace_blocked_arrows.size() );
    assert( level < _less_than_trace_activators.size() );

    const auto v = _less_than_trace_activators[ level ].var();

    _less_than_error_solver.assert_formula( union_sorted( s.literals(), prime( t.literals() ) ).negate().activate( v ) );
    _less_than_consecution_solver.assert_formula( union_sorted( prime( t.literals() ), circle( s.literals() ) ).negate().activate( v ) );

    _less_than_trace_blocked_arrows[ level ].emplace_back( std::move( s ), std::move( t ) );
}

std::vector< std::vector< literal > > verifier_split::build_counterexample( cex_handle root )
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

bool verifier_split::propagate_equality()
{
    logger::log_line_debug( "Propagating equality to level {}", depth() );

    assert( depth() < _equality_trace_blocked_arrows.size() );

    auto pushed_whole_frame = false;

    // If
    //   c /\ TF[ k - 1 ]( X, X° ) /\ TF[ k - 1 ]( X°, X' ) /\ d'
    // is unsatisfiable, we can push (c, d') to TF[ k ].

    for ( int i = 1; i < depth(); ++i )
    {
        auto pushed_all = true;

        // The copy is done since the _trace_blocked_arrows[ i ] will be changed
        // during the forthcoming iteration.
        const auto arrows = _equality_trace_blocked_arrows[ i ];

        for ( const auto& [ c, d ] : arrows )
        {
            if ( !has_equality_middle_point( c.literals(), d.literals(), i + 1 ) )
            {
                auto [ gen_c, gen_d ] = equality_generalize_from_core( c.literals(), d.literals(), i + 1 );
                block_equality_arrow_at( cube{ std::move( gen_c ), is_sorted }, cube{ std::move( gen_d ), is_sorted }, i + 1 );
            }
            else
            {
                pushed_all = false;
            }
        }

        if ( pushed_all )
            pushed_whole_frame = true;
    }

    log_equality_trace_content();

    return pushed_whole_frame;
}

bool verifier_split::propagate_less_than()
{
    logger::log_line_debug( "Propagating less-than to level {}", depth() );

    assert( depth() < _less_than_trace_blocked_arrows.size() );
    assert( _less_than_trace_blocked_arrows[ depth() ].empty() );

    auto pushed_whole_frame = false;

    // If
    //   c /\ TF[ k - 1 ]( X, X° ) /\ TF[ k - 1 ]( X°, X' ) /\ d'
    // is unsatisfiable, we can push (c, d') to TF[ k ].

    for ( int i = 1; i < depth(); ++i )
    {
        // The copy is done since the _trace_blocked_arrows[ i ] will be changed
        // during the forthcoming iteration.
        const auto arrows = _less_than_trace_blocked_arrows[ i ];

        for ( const auto& [ c, d ] : arrows )
        {
            if ( !has_less_than_middle_point( c.literals(), d.literals(), i + 1 ) )
            {
                auto [ gen_c, gen_d, gen_level ] = less_than_generalize_from_core( c.literals(), d.literals(), i + 1 );
                block_less_than_arrow_at( cube{ std::move( gen_c ), is_sorted }, cube{ std::move( gen_d ), is_sorted }, gen_level, i );
            }
        }

        if ( _less_than_trace_blocked_arrows[ i ].empty() )
            pushed_whole_frame = true;
    }

    log_less_than_trace_content();

    return pushed_whole_frame;
}

void verifier_split::log_equality_trace_content() const
{
    auto line = std::format( "= {}:", depth() );

    for ( int i = 1; i <= depth(); ++i )
        line += std::format( " {}", _equality_trace_blocked_arrows[ i ].size() );

    logger::log_line_loud( "{}", line );
}

void verifier_split::log_less_than_trace_content() const
{
    auto line = std::format( "< {}:", depth() );

    for ( int i = 1; i <= depth(); ++i )
        line += std::format( " {}", _less_than_trace_blocked_arrows[ i ].size() );

    logger::log_line_loud( "{}", line );
}

// Returns true if cube contains only state variables. Used for assertions
// only.
bool verifier_split::is_state_cube( std::span< const literal > literals ) const
{
    const auto is_state_var = [ & ]( variable var )
    {
        const auto [ type, _ ] = _system->get_var_info( var );
        return type == var_type::state;
    };

    return std::ranges::all_of( literals, [ & ]( literal lit ){ return is_state_var( lit.var() ); } );
}

bool verifier_split::is_input_cube( std::span< const literal > literals ) const
{
    const auto is_input_var = [ & ]( variable var )
    {
        const auto [ type, _ ] = _system->get_var_info( var );
        return type == var_type::input;
    };

    return std::ranges::all_of( literals, [ & ]( literal lit ){ return is_input_var( lit.var() ); } );
}
