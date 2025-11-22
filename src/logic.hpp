#pragma once

#include <cassert>
#include <string>
#include <algorithm>
#include <iterator>
#include <vector>
#include <span>
#include <optional>
#include <format>

class variable
{
    friend class variable_range;
    friend class variable_store;
    friend class literal;

    int _id;

    explicit variable( int id ) : _id{ id }
    {
        assert( id > 0 );
    }

public:
    [[nodiscard]] int id() const { return _id; }

    friend auto operator<=>( variable, variable ) = default;
};

class variable_range
{
    friend class variable_store;

    int _begin;
    int _end;

    // Construct a range representing variables in range [begin, end).
    variable_range( int begin, int end ) : _begin{ begin }, _end{ end }
    {
        assert( begin > 0 );
        assert( begin <= end );
    }

    class iterator
    {
        int _i;

    public:
        using iterator_category = std::bidirectional_iterator_tag;
        using difference_type   = int;
        using value_type        = variable;
        using pointer           = const variable*;
        using reference         = const variable&;

        iterator() : _i{ 0 } {}
        explicit iterator( int i ) : _i{ i } {}

        variable operator*() const { return variable{ _i }; }
        iterator& operator++() { ++_i; return *this; }
        iterator& operator--() { --_i; return *this; }

        iterator operator++( int )
        {
            const auto copy = *this;
            operator++();
            return copy;
        }

        iterator operator--( int )
        {
            const auto copy = *this;
            operator--();
            return copy;
        }

        friend auto operator<=>( iterator, iterator ) = default;
    };

public:

    [[nodiscard]] int size() const { return _end - _begin; }

    [[nodiscard]] bool contains( variable var ) const
    {
        return _begin <= var.id() && var.id() < _end;
    }

    [[nodiscard]] variable nth( int n ) const
    {
        const auto var = variable{ _begin + n };
        assert( contains( var ) );
        return var;
    }

    [[nodiscard]] int offset( variable var ) const
    {
        assert( contains( var ) );
        return var.id() - _begin;
    }

    [[nodiscard]] iterator begin() const { return iterator{ _begin }; }
    [[nodiscard]] iterator end() const { return iterator{ _end }; }
};

class variable_store
{
    int _next_id = 1;

public:
    variable_store() = default;

    variable make()
    {
        return variable{ _next_id++ };
    }

    [[nodiscard]] variable_range make_range( int n )
    {
        const auto fst = _next_id;

        _next_id += n;

        const auto snd = _next_id;

        return { fst, snd };
    }
};

class literal
{
    int _value;

    explicit literal( int value ) : _value{ value } {}

public:
    explicit literal( variable var, bool positive = true ) : _value{ var.id() }
    {
        if ( !positive )
            _value *= -1;
    }

    static literal separator;

    friend auto operator<=>( literal, literal ) = default;

    [[nodiscard]] int value() const { return _value; }
    [[nodiscard]] variable var() const { return variable{ std::abs( _value ) }; }
    [[nodiscard]] bool positive() const { return _value >= 0; }

    friend literal operator!( literal lit )
    {
        return literal{ -lit._value };
    }

    [[nodiscard]] literal substitute( variable var ) const
    {
        return literal{ var, positive() };
    }

    [[nodiscard]]
    std::string to_string() const
    {
        if ( positive() )
            return std::to_string( _value );
        else
            return std::format( "¬{}", std::abs( _value ) );
    }
};

inline literal literal::separator{ 0 };

class cube;

class cnf_formula
{
    // Literals are stored in DIMACS format, clauses are terminated by zeroes.
    std::vector< literal > _literals;

public:
    static cnf_formula constant( bool value )
    {
        if ( value )
            return cnf_formula{};

        auto contradiction = cnf_formula{};
        contradiction.add_clause( {} );

        return contradiction;
    }

    static cnf_formula clause( std::span< const literal > c )
    {
        auto f = cnf_formula{};
        f.add_clause( c );

        return f;
    }

    void add_clause( std::span< const literal > clause )
    {
        // TODO: Do we want the reserve here?
        _literals.reserve( _literals.size() + clause.size() + 1 );
        _literals.insert( _literals.end(), clause.begin(), clause.end() );
        _literals.push_back( literal::separator );
    }

    void add_clause( literal l1 )
    {
        _literals.emplace_back( l1 );
        _literals.emplace_back( literal::separator );
    }

    void add_clause( literal l1, literal l2 )
    {
        _literals.emplace_back( l1 );
        _literals.emplace_back( l2 );
        _literals.emplace_back( literal::separator );
    }

    void add_clause( literal l1, literal l2, literal l3 )
    {
        _literals.emplace_back( l1 );
        _literals.emplace_back( l2 );
        _literals.emplace_back( l3 );
        _literals.emplace_back( literal::separator );
    }

    [[nodiscard]] const std::vector< literal >& literals() const { return _literals; }

    [[nodiscard]] cnf_formula map( const std::regular_invocable< literal > auto& f ) const
    {
        auto res = cnf_formula{};
        res._literals.reserve( _literals.size() );

        for ( const auto lit : _literals )
            res._literals.push_back( lit == literal::separator ? literal::separator : f( lit ) );

        return res;
    }

    void transform( const std::regular_invocable< literal > auto& f )
    {
        for ( auto& lit : _literals )
            if ( lit != literal::separator )
                lit = f( lit );
    }

    [[nodiscard]]
    cnf_formula activate( variable activator ) const
    {
        auto res = cnf_formula{};
        res._literals.reserve( _literals.size() );

        for ( const auto lit : _literals )
        {
            if ( lit == literal::separator )
                res._literals.push_back( !literal{ activator } );

            res._literals.push_back( lit );
        }

        return res;
    }

    [[nodiscard]]
    cube as_cube() const;
};

// Representation of cubes makes use of literal ordering which is more
// complicated than comparing its underlying integer value. We order literals
// lexicographically first on their absolute value and second on their sign.
// This means that, given variables with values 1, 2 and 3, the following
// vectors are ordered:
//   1, 2, 3
//   -1, 2, 3
//   1, -2, 2, 3
// while the following are not:
//   2, 1
//   -2, 1, 3
//   1, -1, 2, 3
// TODO: Check whether we want this, perhaps it's needlessly complicated and
//       the usual integer ordering suffices?

inline bool cube_literal_lt( literal l1, literal l2 )
{
    return ( l1.var().id() < l2.var().id() ) ||
           ( l1.var().id() == l2.var().id() && !l1.positive() && l2.positive() );
}

class cube
{
    std::vector< literal > _literals;

public:
    cube() = default;

    explicit cube( std::vector< literal > literals ) : _literals{ std::move( literals ) }
    {
        std::ranges::sort( _literals, cube_literal_lt );
    };

    friend auto operator<=>( const cube&, const cube& ) = default;

    [[nodiscard]] const std::vector< literal >& literals() const { return _literals; }

    // Returns true if this syntactically subsumes that, i.e. if literals in
    // this form a subset of literals in that. Note that c.subsumes( d ) = true
    // guarantees that d entails c.
    [[nodiscard]]
    bool subsumes( const cube& that ) const
    {
        return std::ranges::includes( that._literals, _literals, cube_literal_lt );
    }

    // Returns the cube negated as a cnf_formula containing a single clause.
    [[nodiscard]]
    cnf_formula negate() const
    {
        auto f = cnf_formula{};
        f.add_clause( _literals );

        f.transform( []( literal lit )
        {
            return !lit;
        } );

        return f;
    }

    [[nodiscard]]
    bool contains( literal lit ) const
    {
        // TODO: Sequential search is probably faster here...
        return std::ranges::binary_search( _literals, lit, cube_literal_lt );
    }

    // Assuming the cube doesn't contain a pair of literals with the same
    // variable but different polarities, return the literal in which the given
    // variable appears in the cube (or nothing if the variable doesn't appear
    // at all).
    [[nodiscard]]
    std::optional< literal > find( variable var ) const
    {
        const auto lit = literal{ var };

        if ( contains( lit ) )
            return lit;
        if ( contains( !lit ) )
            return !lit;

        return {};
    }

    [[nodiscard]]
    std::string to_string() const
    {
        auto res = std::string{};
        auto sep = "";

        for ( const auto lit : _literals )
        {
            res += sep + lit.to_string();
            sep = " ∧ ";
        }

        return res;
    }
};

inline cube cnf_formula::as_cube() const
{
    // Assert that this is indeed a cube.
    assert( _literals.size() % 2 == 0 );
    assert( std::ranges::count( _literals, literal::separator ) == _literals.size() / 2 );

    auto lits = std::vector< literal >{};

    for ( const auto lit : _literals )
        if ( lit != literal::separator )
            lits.push_back( lit );

    return cube{ lits };
}
