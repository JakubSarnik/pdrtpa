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

cnf_formula build_init( const context& ctx )
{
    // TODO
}

cnf_formula build_trans( const context& ctx )
{
    // TODO
}

cnf_formula build_error( const context& ctx )
{

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

    return context
    {
        .preprocessed_aiger = info,
        .input_vars = store.make_range( static_cast< int >( info.aig->num_inputs ) ),
        .state_vars = store.make_range( num_state_vars ),
        .next_state_vars = store.make_range( num_state_vars ),
        .and_vars = store.make_range( static_cast< int >( info.aig->num_ands ) )
    };
}

transition_system build_from_context( const context& ctx )
{
    auto init = build_init( ctx );
    auto trans = build_trans( ctx );
    auto error = build_error( ctx );

    // TODO: We need to build a translation table from aiger latch literals
    //       to variable offsets, preferably in make_context, and store the
    //       table (in the context probably), together with a function
    //       from_aiger_lit.

    // TODO: Return the system
}

std::expected< transition_system, std::string > build_from_aiger( variable_store& store, aiger& aig )
{
    return make_aiger_info( aig ).transform( [ & ]( const aiger_info& info )
    {
        return build_from_context( make_context( store, info ) );
    } );
}

}
