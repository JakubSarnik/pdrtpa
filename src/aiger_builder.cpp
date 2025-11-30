#include "aiger_builder.hpp"
#include <limits>

namespace builder
{

namespace
{

aiger_literal get_error_literal( const aiger_info& info )
{
    return ( info.aig->num_outputs > 0 ? info.aig->outputs[ 0 ] : info.aig->bad[ 0 ] ).lit;
}

bool is_true( const aiger_info& info, aiger_literal lit )
{
    return info.true_literals.contains( lit );
}

bool is_false( const aiger_info& info, aiger_literal lit )
{
    return info.true_literals.contains( aiger_not( lit ) );
}

bool is_decided( const aiger_info& info, aiger_literal lit )
{
    return is_true( info, lit ) || is_false( info, lit );
}

bool influences_error( const aiger_info& info, aiger_literal lit )
{
    return !is_decided( info, lit ) && info.error_coi.contains( lit );
}

void propagate_trues( aiger_info& info )
{
    info.true_literals.emplace( aiger_true );

    for ( auto i = 0u; i < info.aig->num_ands; ++i )
    {
        const auto [ lhs, rhs0, rhs1 ] = info.aig->ands[ i ];

        if ( is_true( info, rhs0 ) && is_true( info, rhs1 ) )
            info.true_literals.emplace( lhs );
        else if ( is_false( info, rhs0 ) || is_false( info, rhs1 ) )
            info.true_literals.emplace( aiger_not( lhs ) );
    }
}

void determine_coi( aiger_info& info )
{
    const auto error_literal = get_error_literal( info );

    if ( is_decided( info, error_literal ) )
        return;

    auto required = std::unordered_set< aiger_literal >{ error_literal };
    auto changed = true;

    while ( changed )
    {
        changed = false;

        assert( info.aig->num_ands <= std::numeric_limits< int >::max() );

        for ( auto i = static_cast< int >( info.aig->num_ands ) - 1; i >= 0; --i )
        {
            const auto [ lhs, rhs0, rhs1 ] = info.aig->ands[ i ];

            if ( !required.contains( lhs ) && !required.contains( aiger_not( lhs ) ) )
                continue;

            if ( is_decided( info, lhs ) )
                continue;

            const auto [ _it0, inserted_rhs0 ] = required.insert( rhs0 );
            const auto [ _it1, inserted_rhs1 ] = required.insert( rhs1 );

            changed |= inserted_rhs0 || inserted_rhs1;
        }

        for ( auto i = 0u; i < info.aig->num_latches; ++i )
        {
            const auto& latch = info.aig->latches[ i ];

            if ( required.contains( latch.lit ) || required.contains( aiger_not( latch.lit ) ) )
            {
                const auto [ _it, inserted ] = required.insert( latch.next );
                changed |= inserted;
            }
        }
    }

    for ( auto i = 0u; i < info.aig->num_latches; ++i )
    {
        const auto lit = info.aig->latches[ i ].lit;

        if ( required.contains( lit ) || required.contains( aiger_not( lit ) ) )
            info.error_coi.insert( lit );
    }
}

literal from_aiger_lit( const context& ctx, aiger_literal lit )
{
    const auto from_aiger_var = [ & ]( aiger_literal var )
    {
        // The aiger lib expects this to be a positive literal (i.e. a variable).
        assert( var % 2 == 0 );
        assert( var >= 2 ); // Not constants true/false

        if ( const auto *ptr = aiger_is_input( ctx.preprocessed_aiger.aig, var ); ptr )
            return ctx.input_vars.nth( static_cast< int >( ptr - ctx.preprocessed_aiger.aig->inputs ) );
        if ( const auto *ptr = aiger_is_latch( ctx.preprocessed_aiger.aig, var ); ptr )
            return assert( ctx.state_vars_table.contains( var ) ), ctx.state_vars_table.at( var );
        if ( const auto *ptr = aiger_is_and( ctx.preprocessed_aiger.aig, var ); ptr )
            return ctx.and_vars.nth( static_cast< int >( ptr - ctx.preprocessed_aiger.aig->ands ) );

        assert( false && "Unreachable code reached" );
        std::unreachable();
    };

    return literal
    {
        from_aiger_var( aiger_strip( lit ) ),
        aiger_sign( lit ) == 1
    };
}

// Turn an Aiger declaration
//   lhs = rhs0 /\ rhs1
// into a set of clauses using a Tseitin transformation. This must take care
// when either of rhs0/rhs1 is a constant 0 (false) or 1 (true).
void clausify_and( const context& ctx, const aiger_and& conj, cnf_formula& result )
{
    const auto mk_lit = [ & ]( aiger_literal lit )
    {
        return from_aiger_lit( ctx, lit );
    };

    const auto make_equivalence = [ & ]( aiger_literal x, aiger_literal y ){
        // x = y [i.e. x <-> y]
        // ~> (x -> y) /\ (y -> x)
        // ~> (-x \/ y) /\ (-y \/ x)

        result.add_clause( !mk_lit( x ), mk_lit( y ) );
        result.add_clause( !mk_lit( y ), mk_lit( x ) );
    };

    const auto [ lhs, rhs0, rhs1 ] = conj;

    assert( !is_decided( ctx.preprocessed_aiger, lhs ) );

    // It cannot happen that both rhs0 and rhs1 are true (otherwise lhs would
    // be decided as true) or either of them is false (lhs would be decided
    // as false).

    assert( !( is_true( ctx.preprocessed_aiger, rhs0 ) && is_true( ctx.preprocessed_aiger, rhs1 ) ) );
    assert( !is_false( ctx.preprocessed_aiger, rhs0 ) );
    assert( !is_false( ctx.preprocessed_aiger, rhs1 ) );

    if ( is_true( ctx.preprocessed_aiger, rhs0 ) )
        make_equivalence( lhs, rhs1 );
    else if ( is_true( ctx.preprocessed_aiger, rhs1 ) )
        make_equivalence( lhs, rhs0 );
    else
    {
        // lhs = rhs0 /\ rhs1
        // ~> (lhs -> rhs0) /\ (lhs -> rhs1) /\ (rhs0 /\ rhs1 -> lhs)
        // ~> (-lhs \/ rhs0) /\ (-lhs \/ rhs1) /\ (-rhs0 \/ -rhs1 \/ lhs)

        result.add_clause( !mk_lit( lhs ), mk_lit( rhs0 ) );
        result.add_clause( !mk_lit( lhs ), mk_lit( rhs1 ) );
        result.add_clause( !mk_lit( rhs0 ), !mk_lit( rhs1 ), mk_lit( lhs ) );
    }
}

// Do a reverse traversal from the Aiger literals representing the results
// through all the ANDs and ending with leaves consisting of state variables
// and inputs.
//
// NOTE: Aiger literals are the numbers in the aiger file
// ([0 .. 2 * (aig.maxvar) + 1]; 0 = false, 1 = true), which does NOT
// correspond to our variable ordering.
//
// Notably, aiger literal's parity denotes whether it's positive (even)
// or negative (odd).
cnf_formula clausify_subgraph( const context& ctx, std::unordered_set< aiger_literal > required )
{
    auto result = cnf_formula{};

    for ( auto i = static_cast< int >( ctx.preprocessed_aiger.aig->num_ands ) - 1; i >= 0; --i )
    {
        const auto conj = ctx.preprocessed_aiger.aig->ands[ i ];
        const auto [ lhs, rhs0, rhs1 ] = conj;

        if ( !required.contains( lhs ) && !required.contains( aiger_not( lhs ) ) )
            continue;

        if ( is_decided( ctx.preprocessed_aiger, lhs ) )
            continue;

        // If lhs is a required and not decided state variable, it must
        // influence the error, otherwise we are doing work for nothing.

        assert( !aiger_is_latch( ctx.preprocessed_aiger.aig, lhs ) ||
            influences_error( ctx.preprocessed_aiger, lhs ) );

        clausify_and( ctx, conj, result );

        required.insert( rhs0 );
        required.insert( rhs1 );
    }

    return result;
}

cnf_formula build_init( const context& ctx )
{
    auto init = cnf_formula{};

    for ( auto i = 0u; i < ctx.preprocessed_aiger.aig->num_latches; ++i )
    {
        const auto latch = ctx.preprocessed_aiger.aig->latches[ i ];
        const auto lit = latch.lit;
        const auto reset = latch.reset;

        // In Aiger 1.9, the reset can be either 0 (initialized as false),
        // 1 (initialized as true) or equal to the latch literal, which means
        // that the latch has a nondeterministic initial value.

        if ( influences_error( ctx.preprocessed_aiger, lit ) && aiger_is_constant( reset ) )
            init.add_clause( literal{ ctx.state_vars_table.at( lit ), reset == aiger_true } );
    }

    return init;
}

cnf_formula build_trans( const context& ctx )
{
    return cnf_formula::constant( false ); // TODO
}

cnf_formula build_error( const context& ctx )
{
    const auto error_literal = get_error_literal( ctx.preprocessed_aiger );

    if ( is_true( ctx.preprocessed_aiger, error_literal ) )
        return cnf_formula::constant( true );
    if ( is_false( ctx.preprocessed_aiger, error_literal ) )
        return cnf_formula::constant( false );

    auto error = clausify_subgraph( ctx, { error_literal } );

    // An error happens when the error literal is true.
    error.add_clause( from_aiger_lit( ctx, error_literal ) );

    return error;
}

}

std::expected< aiger_info, std::string > make_aiger_info( aiger& aig )
{
    if ( aig.num_outputs + aig.num_bad != 1 )
        return std::unexpected( std::format( "The input AIG has to contain precisely"
                                             " one output (aiger <1.9) or precisely one bad specification"
                                             " (aiger 1.9). The input contains {} outputs and {} bad specifications.",
                                             aig.num_outputs, aig.num_bad ));

    if ( aig.num_fairness > 0 || aig.num_justice > 0 || aig.num_constraints > 0 )
        return std::unexpected( "Aiger justice constraints, fairness properties and invariant"
                                " constraints are not supported." );

    // The function clausify_subgraph depends on ordering of ANDs where each
    // line refers only to literals from previous lines. This, among other
    // things, is ensured by reencoding the AIG.

    if ( aiger_is_reencoded( &aig ) == 0 )
        aiger_reencode( &aig );

    auto info = aiger_info{ .aig = &aig };

    propagate_trues( info );
    determine_coi( info );

    return info;
}

context make_context( variable_store& store, const aiger_info& info )
{
    assert( info.aig->num_inputs <= std::numeric_limits< int >::max() );
    assert( info.aig->num_latches <= std::numeric_limits< int >::max() );
    assert( info.aig->num_ands <= std::numeric_limits< int >::max() );

    auto num_state_vars = 0;

    // TODO: Is this possible? We remove every determined state variable!
    for ( auto i = 0u; i < info.aig->num_latches; ++i )
        if ( influences_error( info, info.aig->latches[ i ].lit ) )
            ++num_state_vars;

    const auto input_vars = store.make_range( static_cast< int >( info.aig->num_inputs ) );
    const auto state_vars = store.make_range( num_state_vars );
    const auto next_state_vars = store.make_range( num_state_vars );
    const auto and_vars = store.make_range( static_cast< int >( info.aig->num_ands ) );

    auto state_vars_table = std::unordered_map< aiger_literal, variable >{};
    auto j = 0;

    for ( auto i = 0u; i < info.aig->num_latches; ++i )
        if ( const auto lit = info.aig->latches[ i ].lit; influences_error( info, lit ) )
            state_vars_table.emplace( lit, state_vars.nth( j++ ) );

    return context
    {
        .preprocessed_aiger = info,
        .input_vars = input_vars,
        .state_vars = state_vars,
        .next_state_vars = next_state_vars,
        .and_vars = and_vars,
        .state_vars_table = std::move( state_vars_table )
    };
}

transition_system build_from_context( const context& ctx )
{
    auto initial_cube = std::vector< bool >{};

    for ( auto i = 0u; i < ctx.preprocessed_aiger.aig->num_latches; ++i )
        if ( const auto reset = ctx.preprocessed_aiger.aig->latches[ i ].reset; aiger_is_constant( reset ) )
            initial_cube.push_back( reset == aiger_true );

    return transition_system
    {
        ctx.input_vars, ctx.state_vars, ctx.next_state_vars, ctx.and_vars, std::move( initial_cube ),
        build_init( ctx ), build_trans( ctx ), build_error( ctx )
    };
}

std::expected< transition_system, std::string > build_from_aiger( variable_store& store, aiger& aig )
{
    return make_aiger_info( aig ).transform( [ & ]( const aiger_info& info )
    {
        return build_from_context( make_context( store, info ) );
    } );
}

}
