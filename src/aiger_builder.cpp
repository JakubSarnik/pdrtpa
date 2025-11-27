#include "aiger_builder.hpp"

namespace builder
{

namespace
{

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

aiger_literal get_error_literal( const aiger_info& info )
{
    return ( info.aig->num_outputs > 0 ? info.aig->outputs[ 0 ] : info.aig->bad[ 0 ] ).lit;
}

}

}
