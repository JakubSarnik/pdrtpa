#pragma once

#include "logic.hpp"
#include "transition_system.hpp"
#include "solver.hpp"
#include "verifier.hpp"
#include <vector>
#include <optional>
#include <random>

// cex_handle, cex_entry, cex_pool and proof_obligation are the same as in
// verifier.hpp
// TODO: If keeping this file only, copy over

class verifier_split
{
public:
    using result_t = std::optional< std::vector< std::vector< literal > > >;

private:
    variable_store* _store;
    std::default_random_engine _random;

    // We need to solve the following types of formulae:
    //   1. I(X) /\ TF=[i](X, X') /\ ~P(X') in the main loop (blocking phase),
    //   2. I(X) /\ TF<[i](X, X') /\ ~P(X') in the main loop (blocking phase),
    //   3. s /\ TF=[i](X, X°) /\ TF=[i](X°, X') /\ t' in the
    //     - main loop (propagation to TF=[i + 1])
    //       [if we propagate equality frames],
    //     - obligation solver (equality obligation solver),
    //   4. s /\ TF=[i](X, X°) /\ TF<[i](X°, X') /\ t' in the
    //     - main loop (propagation to TF<[i + 1]),
    //     - obligation solver (less-than obligation solver).
    //
    // We have a special case of 1 before the main loop for i = 0:
    //   I(X) /\ T(X, Y, X') /\ ~P(X'),
    // and a similar special case of 2 for i = 0:
    //   I(X) /\ ~P(X').
    //
    // For equality proof obligations at the first level, the formula 3 refers
    // to the frame TF=[0] = T(X, Y, X'), which means we need to check the
    // formula
    //   s /\ T(X, Y1, X°) /\ T(X°, Y2, X') /\ t'.
    //   [Note the two different variants of Y!]
    //
    // Similarly, for less-than proof obligations at the first level, the
    // formula 4 refers to both TF=[0] = T(X, Y, X') and TF<[i] = id(X, X'),
    // which leads to the formula
    //   s /\ T(X, Y, X') /\ t'.

    solver _equality_error_solver; // Solves I(X) /\ TF[i]=(X, X') /\ ~P'
    solver _less_than_error_solver; // Solves I(X) /\ TF[i]<(X, X') /\ ~P'
    solver _one_step_solver; // Solves s /\ T(X, Y, X') /\ t'
    solver _two_steps_solver; // Solves s /\ T(X, Y1, X°) /\ T(X°, Y2, X') /\ t'
    solver _equality_consecution_solver; // Solves s /\ TF=[i](X, X°) /\ TF=[i](X°, X') /\ t'
    solver _less_than_consecution_solver; // Solves s /\ TF=[i](X, X°) /\ TF<[i](X°, X') /\ t'

    const transition_system* _system = nullptr;
    cube _init_cube;

    variable_range _middle_state_vars; // X°
    variable_range _left_input_vars;   // Y1 = Y
    variable_range _right_input_vars;  // Y2
    variable_range _right_aux_vars;    // Needed to separate the two instances of T

    cnf_formula _left_trans; // T(X, Y1, X°)
    cnf_formula _right_trans; // T(X°, Y2, X')

    // TODO: Store only if we propagate equality frames
    std::vector< std::vector< std::pair< cube, cube > > > _equality_trace_blocked_arrows;
    std::vector< std::vector< std::pair< cube, cube > > > _less_than_trace_blocked_arrows;

    std::vector< literal > _equality_trace_activators; // Not cumulative
    std::vector< literal > _less_than_trace_activators; // Cumulative

    cex_pool _cexes;

    [[nodiscard]] int depth() const
    {
        assert( _equality_trace_blocked_arrows.size() <= std::numeric_limits< int >::max() );
        assert( _equality_trace_blocked_arrows.size() == _less_than_trace_blocked_arrows.size() );
        assert( _less_than_trace_blocked_arrows.size() == _less_than_trace_activators.size() );
        assert( _less_than_trace_activators.size() == _equality_trace_activators.size() );

        return static_cast< int >( _equality_trace_blocked_arrows.size() ) - 1;
    }

    void push_frame()
    {
        assert( _equality_trace_blocked_arrows.size() == _less_than_trace_blocked_arrows.size() );
        assert( _less_than_trace_blocked_arrows.size() == _less_than_trace_activators.size() );
        assert( _less_than_trace_activators.size() == _equality_trace_activators.size() );

        _equality_trace_blocked_arrows.emplace_back();
        _equality_trace_activators.emplace_back( _store->make() );

        _less_than_trace_blocked_arrows.emplace_back();
        _less_than_trace_activators.emplace_back( _store->make() );
    }

    [[nodiscard]] literal equality_activator_at( int level ) const
    {
        assert( 0 <= level && level <= depth() );
        return _equality_trace_activators[ level ];
    }

    [[nodiscard]] std::span< const literal > less_than_activators_from( int level ) const
    {
        assert( 0 <= level && level <= depth() );
        return std::span{ _less_than_trace_activators }.subspan( level );
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

        for ( auto lit : literals )
            if ( from.contains( lit.var() ) )
                lits.push_back( shift_literal( from, to, lit ) );

        return lits;
    }

    [[nodiscard]] literal prime( literal lit ) const
    {
        return shift_literal( _system->state_vars(), _system->next_state_vars(), lit );
    }

    [[nodiscard]] std::vector< literal > prime( std::span< const literal > literals ) const
    {
        return shift_literals( _system->state_vars(), _system->next_state_vars(), literals );
    }

    [[nodiscard]] std::vector< literal > circle( std::span< const literal > literals ) const
    {
        return shift_literals( _system->state_vars(), _middle_state_vars, literals );
    }

    [[nodiscard]] literal circle( literal lit ) const
    {
        return shift_literal( _system->state_vars(), _middle_state_vars, lit );
    }

    [[nodiscard]] std::vector< literal > unprime( std::span< const literal > literals ) const
    {
        return shift_literals( _system->next_state_vars(), _system->state_vars(), literals );
    }

    [[nodiscard]] literal unprime( literal lit ) const
    {
        return shift_literal( _system->next_state_vars(), _system->state_vars(), lit );
    }

    [[nodiscard]] std::vector< literal > uncircle( std::span< const literal > literals ) const
    {
        return shift_literals( _middle_state_vars, _system->state_vars(), literals );
    }

    [[nodiscard]] literal uncircle( literal lit ) const
    {
        return shift_literal( _middle_state_vars, _system->state_vars(), lit );
    }

    const cube& get_s( const proof_obligation& po )
    {
        return _cexes.get( po.handle() ).s_state_vars;
    }

    const cube& get_t( const proof_obligation& po )
    {
        return _cexes.get( po.handle() ).t_state_vars;
    }

    const std::optional< cube >& get_inputs( const proof_obligation& po )
    {
        return _cexes.get( po.handle() ).input_vars;
    }

    solver& get_equality_solver_for( int level )
    {
        assert( 0 <= level && level <= depth() + 1 );

        switch ( level )
        {
            case 0:
                return _one_step_solver;
            case 1:
                return _two_steps_solver;
            default:
                return _equality_consecution_solver;
        }
    }

    solver& get_less_than_solver_for( int level )
    {
        assert( 0 <= level && level <= depth() + 1 );

        switch ( level )
        {
            case 0:
            case 1:
                return _one_step_solver;
            default:
                return _equality_consecution_solver;
        }
    }

    void initialize();
    result_t check();
    result_t check_trivial_cases();

    std::optional< cex_handle > get_equality_error_cex();
    std::optional< cex_handle > get_less_than_error_cex();

    bool solve_equality_obligation( const proof_obligation& po );
    bool solve_less_than_obligation( const proof_obligation& po );

    bool has_edge( std::span< const literal > c, std::span< const literal > d );
    bool has_equality_middle_point( std::span< const literal > c, std::span< const literal > d, int level );
    bool has_less_than_middle_point( std::span< const literal > c, std::span< const literal > d, int level );

    bool has_concrete_edge( const proof_obligation& po );
    std::optional< std::pair< cex_handle, cex_handle > > split_equality_path( const proof_obligation& po );
    std::optional< std::pair< cex_handle, cex_handle > > split_less_than_path( const proof_obligation& po );
    bool has_path_of_length_two( const proof_obligation& po );

    std::optional< std::pair< proof_obligation, proof_obligation > > split_equality_obligation( const proof_obligation& po );
    std::optional< std::pair< proof_obligation, proof_obligation > > split_less_than_obligation( const proof_obligation& po );

    auto generalize_blocked_equality_arrow( std::span< const literal > s, std::span< const literal > t, int level )
        -> std::tuple< std::vector< literal >, std::vector< literal >, int >;
    auto equality_generalize_from_core( std::span< const literal > s, std::span< const literal > t, int level )
        -> std::tuple< std::vector< literal >, std::vector< literal >, int >;

    auto generalize_blocked_less_than_arrow( std::span< const literal > s, std::span< const literal > t, int level )
        -> std::tuple< std::vector< literal >, std::vector< literal >, int >;
    auto less_than_generalize_from_core( std::span< const literal > s, std::span< const literal > t, int level )
        -> std::tuple< std::vector< literal >, std::vector< literal >, int >;

    void block_equality_arrow_at( cube s, cube t, int level );
    void block_less_than_arrow_at( cube s, cube t, int level, int start_from = 1 );

    std::vector< std::vector< literal > > build_counterexample( cex_handle root );

    bool propagate_equality();
    bool propagate_less_than();

    void log_equality_trace_content() const;
    void log_less_than_trace_content() const;

    [[nodiscard]] [[maybe_unused]] bool is_state_cube( std::span< const literal > literals ) const;
    [[nodiscard]] [[maybe_unused]] bool is_input_cube( std::span< const literal > literals ) const;

public:
    explicit verifier_split( variable_store& store, const transition_system& system, unsigned int seed ) :
        _store{ &store },
        _random{ seed },
        _system{ &system },
        _init_cube{ system.init().as_cube() },
        _middle_state_vars{ store.make_range( system.state_vars().size() ) },
        _left_input_vars{ system.input_vars() },
        _right_input_vars( store.make_range( system.input_vars().size() ) ),
        _right_aux_vars( store.make_range( system.aux_vars().size() ) ),
        _left_trans{ system.trans().map( [ & ]( literal l ){ return make_left_trans( l ); } ) },
        _right_trans{ system.trans().map( [ & ]( literal l ){ return make_right_trans( l ); } ) }
    {}

    verifier_split( const verifier_split& ) = delete;
    verifier_split& operator=( const verifier_split& ) = delete;

    verifier_split( verifier_split&& ) = default;
    verifier_split& operator=( verifier_split&& ) = default;

    ~verifier_split() = default;

    [[nodiscard]] result_t run();
};
