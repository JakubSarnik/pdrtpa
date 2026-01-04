#pragma once

#include "logic.hpp"
#include "transition_system.hpp"
#include "solver.hpp"
#include <concepts>
#include <vector>
#include <optional>

using cex_handle = std::size_t;

struct cex_entry
{
    cube s_state_vars;
    cube t_state_vars; // Unprimed!
    std::optional< cube > input_vars;
    std::optional< cex_handle > left;
    std::optional< cex_handle > right;
};

// TODO: Make this safer and/or more efficient?
class cex_pool
{
    std::vector< cex_entry > _entries;

public:
    // Beware that the handle is invalidated after the next call to clear!
    [[nodiscard]] cex_handle make( cube s_state_vars, cube t_state_vars, std::optional< cube > input_vars = {} )
    {
        _entries.emplace_back( std::move( s_state_vars ), std::move( t_state_vars ), std::move( input_vars ) );
        return _entries.size() - 1;
    }

    [[nodiscard]] cex_entry& get( cex_handle handle )
    {
        assert( handle < _entries.size() );
        return _entries[ handle ];
    }

    void clear()
    {
        _entries.clear();
    }
};

class proof_obligation
{
    // Declared in this order so that the defaulted comparison operator
    // orders by level primarily.
    int _level;
    cex_handle _handle;

public:
    proof_obligation( cex_handle handle, int level ) : _level{ level }, _handle{ handle }
    {
        assert( _level >= 0 );
    };

    friend auto operator<=>( const proof_obligation&, const proof_obligation& ) = default;

    [[nodiscard]] int level() const { return _level; }
    [[nodiscard]] cex_handle handle() const { return _handle; }
};

class verifier
{
public:
    using result_t = std::optional< std::vector< std::vector< literal > > >;

private:
    variable_store* _store;

    // We need to solve the following types of formulae:
    //   1. I(X) /\ TF[i](X, X') /\ ~P(X') in the main loop (blocking phase)
    //   2. TF[i](X, X°) /\ TF[i](X°, X') /\ s /\ t' in the
    //     - main loop (propagation)
    //     - obligation solver
    // We have a few special cases of 1 before the main loop:
    //   1a. I(X) /\ ~P(X)
    //   1b. I(X) /\ T(X, Y, X') /\ ~P(X')
    // And for proof obligations at the first level, the formula 2 refers
    // to the frame TF[0] = id(X, X') \/ T(X, Y, X'):
    //   2a. id(X, X°) /\ id(X°, X') /\ s /\ t' ~> s = t
    //   2b. id(X, X°) /\ T(X°, Y, X') /\ s /\ t' ~>
    //       s /\ T(X, Y, X') /\ t'
    //   2c. T(X, Y, X°) /\ id(X°, X') /\ s /\ t' ~>
    //       s /\ T(X, Y, X°) /\ t° ~>
    //       s /\ T(X, Y, X') /\ t' (i.e. same as 2b)
    //   2d. T(X, Y1, X°) /\ T(X°, Y2, X') /\ s /\ t'
    //       [Note the two different variants of Y!]
    // And finally the proof obligation base case:
    //   3a. s /\ id(X, X') /\ t' ~> s = t
    //   3b. s /\ T(X, Y, X') /\ t'

    solver _error_solver; // Solves I(X) /\ TF[i](X, X') /\ ~P'
    solver _consecution_solver; // Solves TF[i](X, X°) /\ TF[i](X°, X') /\ s /\ t'

    const transition_system* _system = nullptr;
    cube _init_cube;

    variable_range _middle_state_vars; // X°
    variable_range _left_input_vars;   // Y1 = Y
    variable_range _right_input_vars;  // Y2
    variable_range _right_aux_vars;    // Needed to separate the two instances of T

    cnf_formula _left_trans; // T(X, Y1, X°)
    cnf_formula _right_trans; // T(X°, Y2, X')

    using cubes = std::vector< cube >;

    std::vector< cubes > _trace_blocked_cubes;
    std::vector< literal > _trace_activators;
    literal _trans_activator; // Activates T(X, Y, X') in _consecution_solver
    literal _left_trans_activator; // Activates T(X, Y1, X°) in _consecution_solver
    literal _right_trans_activator; // Activates T(X°, Y2, X') in _consecution_solver
    cex_pool _cexes;

    [[nodiscard]] int depth() const
    {
        assert( _trace_blocked_cubes.size() <= std::numeric_limits< int >::max() );
        return static_cast< int >( _trace_blocked_cubes.size() ) - 1;
    }

    void push_frame()
    {
        assert( _trace_blocked_cubes.size() == _trace_activators.size() );

        _trace_blocked_cubes.emplace_back();
        _trace_activators.emplace_back( _store->make() );
    }

    std::span< literal > activators_from( int level )
    {
        assert( 0 <= level && level <= depth() );
        return std::span{ _trace_activators }.subspan( level );
    }

    // T(X, Y, X') -> T(X, Y, X°)
    [[nodiscard]] literal make_left_trans( literal lit ) const
    {
        const auto [ type, pos ] = _system->get_var_info( lit.var() );

        if ( type == var_type::next_state )
            return lit.substitute( _middle_state_vars.nth( pos ) );
        else
            return lit;
    }

    // T(X, Y, X') -> T(X°, Y2, X') (and right aux vars)
    [[nodiscard]] literal make_right_trans( literal lit ) const
    {
        const auto [ type, pos ] = _system->get_var_info( lit.var() );

        switch ( type )
        {
            case var_type::state:
                return lit.substitute( _middle_state_vars.nth( pos ) );
            case var_type::input:
                return lit.substitute( _right_input_vars.nth( pos ) );
            case var_type::auxiliary:
                return lit.substitute( _right_aux_vars.nth( pos ) );
            default:
                return lit;
        }
    }

    [[nodiscard]] static literal shift_literal( variable_range from, variable_range to, literal lit )
    {
        assert( from.contains( lit.var() ) );
        return lit.substitute( to.nth( from.offset( lit.var() ) ) );
    }

    [[nodiscard]] static std::vector< literal > shift_literals( variable_range from, variable_range to,
        std::span< const literal > literals )
    {
        auto lits = std::vector< literal >{};
        // TODO: Consider reserve

        for ( auto lit : literals )
            if ( from.contains( lit.var() ) )
                lits.push_back( shift_literal( from, to, lit ) );

        return lits;
    }

    [[nodiscard]] std::vector< literal > prime( std::span< const literal > literals ) const
    {
        return shift_literals( _system->state_vars(), _system->next_state_vars(), literals );
    }

    [[nodiscard]] std::vector< literal > circle( std::span< const literal > literals ) const
    {
        return shift_literals( _system->state_vars(), _middle_state_vars, literals );
    }

    [[nodiscard]] std::vector< literal > unprime( std::span< const literal > literals ) const
    {
        return shift_literals( _system->next_state_vars(), _system->state_vars(), literals );
    }

    [[nodiscard]] std::vector< literal > uncircle( std::span< const literal > literals ) const
    {
        return shift_literals( _middle_state_vars, _system->state_vars(), literals );
    }

    void initialize();
    result_t check();
    result_t check_trivial_cases();

    std::optional< cex_handle > get_error_cex();
    bool solve_obligation( const proof_obligation& po );

    bool has_concrete_edge( cex_entry& cex );
    bool has_path_of_length_two( cex_entry& cex );
    std::optional< std::pair< proof_obligation, proof_obligation > > split_in_the_middle( const proof_obligation& po );

    void block_arrow_at( const cube& s, const cube& t, int level, int start_from = 1 );

    std::vector< std::vector< literal > > build_counterexample( cex_handle root );

    bool propagate();

    [[nodiscard]] [[maybe_unused]] bool is_state_cube( std::span< const literal > literals ) const;

public:
    explicit verifier( variable_store& store, const transition_system& system ) :
        _store{ &store },
        _system{ &system },
        _init_cube{ system.init().as_cube() },
        _middle_state_vars{ store.make_range( system.state_vars().size() ) },
        _left_input_vars{ system.input_vars() },
        _right_input_vars( store.make_range( system.input_vars().size() ) ),
        _right_aux_vars( store.make_range( system.aux_vars().size() ) ),
        _left_trans{ system.trans().map( [ & ]( literal l ){ return make_left_trans( l ); } ) },
        _right_trans{ system.trans().map( [ & ]( literal l ){ return make_right_trans( l ); } ) },
        _trans_activator{ store.make() },
        _left_trans_activator{ store.make() },
        _right_trans_activator{ store.make() }
    {}

    verifier( const verifier& ) = delete;
    verifier& operator=( const verifier& ) = delete;

    verifier( verifier&& ) = default;
    verifier& operator=( verifier&& ) = default;

    ~verifier() = default;

    [[nodiscard]] result_t run();
};
