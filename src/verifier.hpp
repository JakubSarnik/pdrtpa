#pragma once

#include "logic.hpp"
#include "transition_system.hpp"
#include "solver.hpp"
#include <vector>
#include <optional>

using cex_handle = std::size_t;

struct cex_entry
{
    cube state_vars;
    std::optional< cube > input_vars; // Nullopt if internal node or equality leaf
    cex_handle left = std::numeric_limits< cex_handle >::max();
    cex_handle right = std::numeric_limits< cex_handle >::max();

    [[nodiscard]] bool is_leaf() const
    {
        return left == std::numeric_limits< cex_handle >::max() &&
            right == std::numeric_limits< cex_handle >::max();
    }
};

// TODO: Make this safer and/or more efficient?
class cex_pool
{
    std::vector< cex_entry > _entries;

public:
    // Beware that the handle is invalidated after the next call to clear!
    [[nodiscard]] cex_handle make( cube state_vars, std::optional< cube > input_vars )
    {
        _entries.emplace_back( std::move( state_vars ), std::move( input_vars ) );
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

    solver _error_solver;
    solver _consecution_solver;

    const transition_system* _system = nullptr;
    cube _init_cube;

    using cubes = std::vector< cube >;

    std::vector< cubes > _trace_blocked_cubes;
    std::vector< literal > _trace_activators;

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

    void initialize();
    result_t check();

public:
    explicit verifier( variable_store& store ) noexcept : _store( &store ) {}

    verifier( const verifier& ) = delete;
    verifier& operator=( const verifier& ) = delete;

    verifier( verifier&& ) = default;
    verifier& operator=( verifier&& ) = default;

    ~verifier() = default;

    [[nodiscard]] result_t run( const transition_system& system );
};
