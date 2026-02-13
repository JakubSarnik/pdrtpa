#include "simplifier.hpp"
#include "cadical.hpp"
#include "logic.hpp"
#include <concepts>

namespace
{

class clause_reader : public CaDiCaL::ClauseIterator {
    std::vector< int > _dimacs;

public:
    bool clause( const std::vector< int >& cl ) override
    {
        for ( const auto num : cl )
            _dimacs.emplace_back( num );

        _dimacs.emplace_back( 0 );
        return true;
    }

    [[nodiscard]] cnf_formula formula() const
    {
        return cnf_formula::from_dimacs( _dimacs );
    }
};

void freeze_range( CaDiCaL::Solver& solver, variable_range range )
{
    for ( const auto var : range )
        solver.freeze( var.id() );
}

template < std::same_as< variable_range >... Ranges >
cnf_formula simplify_formula( const cnf_formula& formula, Ranges... ranges_to_freeze )
{
    auto solver = CaDiCaL::Solver{};

    for ( const auto lit : formula.literals() )
        solver.add( lit.value() );

    (freeze_range( solver, ranges_to_freeze ), ...);

    solver.simplify();

    auto reader = clause_reader{};
    solver.traverse_clauses( reader );

    return reader.formula();
}

cnf_formula simplify_init( const transition_system& system )
{
    return simplify_formula( system.init(), system.state_vars() );
}

cnf_formula simplify_trans( const transition_system& system )
{
    return simplify_formula( system.trans(), system.state_vars(), system.next_state_vars(), system.input_vars() );
}

cnf_formula simplify_error( const transition_system& system )
{
    return simplify_formula( system.error(), system.state_vars(), system.input_vars() );
}

}

transition_system simplify( const transition_system& system )
{
    return transition_system{ system.input_vars(), system.state_vars(), system.next_state_vars(), system.aux_vars(),
        system.initial_cube(), simplify_init( system ), simplify_trans( system ), simplify_error( system ) };
}
