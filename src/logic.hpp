#pragma once

#include <cassert>
#include <cmath>
#include <compare>
#include <iterator>

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

    friend auto operator<=>( literal, literal ) = default;
};

inline literal literal::separator{ 0 };
