#include "common.hpp"
#include "logic.hpp"
#include <algorithm>
#include <vector>

TEST_CASE( "Variables have the expected ids" )
{
    auto store = variable_store{};

    auto x = store.make();
    auto y = store.make();

    REQUIRE( x.id() == 1 );
    REQUIRE( y.id() == 2 );
}

TEST_CASE( "Variable store hands out different variables" )
{
    auto store = variable_store{};

    auto x = store.make();
    auto y = store.make();

    REQUIRE( x != y );
}

TEST_CASE( "Variable ranges have the expected sizes" )
{
    auto store = variable_store{};

    SECTION( "Empty range" )
    {
        REQUIRE( store.make_range( 0 ).size() == 0 );
    }

    SECTION( "Unit range" )
    {
        REQUIRE( store.make_range( 1 ).size() == 1 );
    }

    SECTION( "Longer range" )
    {
        REQUIRE( store.make_range( 4 ).size() == 4 );
        REQUIRE( store.make_range( 5 ).size() == 5 );
    }
}

TEST_CASE( "Variable ranges are correctly iterable" )
{
    auto store = variable_store{};
    const auto range = store.make_range( 2 );
    auto it = range.begin();

    REQUIRE( ( *it ).id() == 1 );

    it++; // NOLINT
    REQUIRE( ( *it ).id() == 2 );

    ++it;
    REQUIRE( it == range.end() );

    it--; // NOLINT
    --it;
    REQUIRE( it == range.begin() );
}

TEST_CASE( "Variable ranges are created correctly" )
{
    auto store = variable_store{};

    SECTION( "Empty range has no variables" )
    {
        const auto x = store.make();
        const auto r = store.make_range( 0 );
        const auto y = store.make();

        REQUIRE( r.begin() == r.end() );
        REQUIRE( y.id() == x.id() + 1 );
    }

    SECTION( "Empty range can be created several times without effect" )
    {
        const auto x = store.make();
        static_cast< void >( store.make_range( 0 ) );
        static_cast< void >( store.make_range( 0 ) );
        static_cast< void >( store.make_range( 0 ) );
        const auto y = store.make();

        REQUIRE( y.id() == x.id() + 1 );
    }

    SECTION( "Unit range has one variable" )
    {
        const auto x = store.make();
        const auto r1 = store.make_range( 1 );
        const auto r2 = store.make_range( 1 );
        const auto y = store.make();

        const auto u = *r1.begin();
        const auto v = *r2.begin();

        REQUIRE( r1.begin() != r1.end() );
        REQUIRE( r2.begin() != r2.end() );
        REQUIRE( y.id() == v.id() + 1 );
        REQUIRE( v.id() == u.id() + 1 );
        REQUIRE( u.id() == x.id() + 1 );
    }

    SECTION( "Longer ranges have all variables" )
    {
        const auto r1 = store.make_range( 3 );
        const auto r2 = store.make_range( 2 );

        for ( int i = 0; i < 3; ++i )
            REQUIRE( r1.nth( i ).id() == 1 + i );
        for ( int i = 0; i < 2; ++i )
            REQUIRE( r2.nth( i ).id() == 4 + i );
    }
}

TEST_CASE( "Nth and offset work for ranges" )
{
    auto store = variable_store{};

    static_cast< void >( store.make_range( 1 ) );
    const auto range = store.make_range( 3 );

    REQUIRE( range.nth( 0 ).id() == 2 );
    REQUIRE( range.nth( 1 ).id() == 3 );
    REQUIRE( range.nth( 2 ).id() == 4 );

    REQUIRE( range.offset( range.nth( 0 ) ) == 0 );
    REQUIRE( range.offset( range.nth( 1 ) ) == 1 );
    REQUIRE( range.offset( range.nth( 2 ) ) == 2 );
}

TEST_CASE( "Literals have the expected IDs and values" )
{
    auto store = variable_store{};

    const auto x = store.make();
    const auto y = store.make();

    const auto lx = literal{ x };
    const auto ly = literal{ y };

    REQUIRE( lx.var() == x );
    REQUIRE( lx.value() == 1 );
    REQUIRE( lx.positive() == true );

    REQUIRE( ly.var() == y );
    REQUIRE( ly.value() == 2 );
    REQUIRE( ly.positive() == true );
}

TEST_CASE( "Literals are negated correctly" )
{
    auto store = variable_store{};
    const auto var = store.make();

    SECTION( "Using the constructor" )
    {
        const auto lit = literal{ var, false };

        REQUIRE( lit.var() == var );
        REQUIRE( lit.value() == -1 );
        REQUIRE( lit.positive() == false );
    }

    SECTION( "Using the negation operator" )
    {
        const auto lit = !literal{ var };

        REQUIRE( lit.var() == var );
        REQUIRE( lit.value() == -1 );
        REQUIRE( lit.positive() == false );
    }
}

TEST_CASE( "Literals of different polarity are different" )
{
    auto store = variable_store{};
    const auto var = store.make();
    const auto lit = literal{ var };

    REQUIRE( lit != !lit );
}

TEST_CASE( "Literal substitution works as expected" )
{
    auto store = variable_store{};
    const auto v1 = store.make();
    const auto v2 = store.make();

    const auto lit = literal{ v1 };

    REQUIRE( lit.substitute( v2 ) == literal{ v2 } );
    REQUIRE( ( !lit ).substitute( v2 ) == !literal{ v2 } );
}

TEST_CASE( "CNF formula is built correctly using add_clause" )
{
    auto store = variable_store{};
    auto formula = cnf_formula{};

    REQUIRE( formula.literals().empty() );

    const auto a = literal{ store.make() };
    const auto b = literal{ store.make() };

    formula.add_clause( std::vector{ a, b } );

    REQUIRE( formula.literals() == std::vector{ a, b, literal::separator } );

    formula.add_clause( !a );

    REQUIRE( formula.literals() == std::vector{ a, b, literal::separator, !a, literal::separator } );

    auto c = literal{ store.make() };

    formula.add_clause( c, !c );

    REQUIRE( formula.literals() == std::vector{ a, b, literal::separator, !a, literal::separator,
        c, !c, literal::separator } );

    formula.add_clause( {} );

    REQUIRE( formula.literals() == std::vector{ a, b, literal::separator, !a, literal::separator,
        c, !c, literal::separator, literal::separator } );
}

TEST_CASE( "CNF formula built from clause() can be added to" )
{
    auto store = variable_store{};

    const auto a = literal{ store.make() };
    const auto b = literal{ store.make() };
    const auto c = literal{ store.make() };

    SECTION( "Empty clause" )
    {
        auto f = cnf_formula::clause( std::vector< literal >{} );
        f.add_clause( a, b );
        f.add_clause( c );

        REQUIRE( f.literals() == std::vector{ literal::separator, a, b, literal::separator, c, literal::separator } );
    }

    SECTION( "Non-empty clause" )
    {
        auto f = cnf_formula::clause( std::vector{ a, !b } );
        f.add_clause( !c );

        REQUIRE( f.literals() == std::vector{ a, !b, literal::separator, !c, literal::separator } );
    }
}

TEST_CASE( "Formulas are mapped correctly" )
{
    auto store = variable_store{};
    auto f = cnf_formula{};

    const auto a = literal{ store.make() };
    const auto b = literal{ store.make() };
    const auto c = literal{ store.make() };

    f.add_clause( a, b, b );
    f.add_clause( !b, a, c );
    f.add_clause( !c, c );

    REQUIRE( f.literals() == std::vector{ a, b, b, literal::separator, !b, a, c, literal::separator,
        !c, c, literal::separator } );

    SECTION( "To a constant" )
    {
        const auto d = literal{ store.make() };

        const auto to_d = [=]( literal )
        {
            return d;
        };

        const auto to_neg_d = [=]( literal )
        {
            return !d;
        };

        REQUIRE( f.map( to_d ).literals() ==
            std::vector{ d, d, d, literal::separator, d, d, d, literal::separator, d, d, literal::separator } );

        REQUIRE( f.map( to_neg_d ).literals() ==
            std::vector{ !d, !d, !d, literal::separator, !d, !d, !d, literal::separator, !d, !d, literal::separator } );
    }

    SECTION( "Using a constant substitution" )
    {
        const auto d = literal{ store.make() };

        const auto to_d = [=]( literal lit )
        {
            return lit.substitute( d.var() );
        };

        REQUIRE( f.map( to_d ).literals() == std::vector{ d, d, d, literal::separator, !d, d, d, literal::separator,
            !d, d, literal::separator } );
    }

    SECTION( "Using a non-constant substitution" )
    {
        const auto aa = literal{ store.make() };
        const auto bb = literal{ store.make() };
        const auto cc = literal{ store.make() };

        const auto g = [=]( literal lit )
        {
            return lit.substitute( lit.var() == a.var() ? aa.var() : lit.var() == b.var() ? bb.var() : cc.var() );
        };

        REQUIRE( f.map( g ).literals() == std::vector{ aa, bb, bb, literal::separator, !bb, aa, cc, literal::separator,
            !cc, cc, literal::separator } );
    }

    SECTION( "With literal negation" )
    {
        const auto neg = []( literal lit )
        {
            return !lit;
        };

        REQUIRE( f.map( neg ).literals() == std::vector{ !a, !b, !b, literal::separator, b, !a, !c, literal::separator,
            c, !c, literal::separator } );
    }
}

TEST_CASE( "Formulas are transformed correctly" )
{
    auto store = variable_store{};
    auto f = cnf_formula{};

    const auto a = literal{ store.make() };
    const auto b = literal{ store.make() };
    const auto c = literal{ store.make() };

    f.add_clause( a, b, b );
    f.add_clause( !b, a, c );
    f.add_clause( !c, c );

    const auto old_f = f;

    REQUIRE( f.literals() == std::vector{ a, b, b, literal::separator, !b, a, c, literal::separator,
        !c, c, literal::separator } );

    SECTION( "To a constant" )
    {
        const auto d = literal{ store.make() };

        const auto to_d = [=]( literal )
        {
            return d;
        };

        const auto to_neg_d = [=]( literal )
        {
            return !d;
        };

        SECTION( "to_d" )
        {
            f.transform( to_d );
            REQUIRE( f == old_f.map( to_d ) );
        }

        SECTION( "to_neg_d" )
        {
            f.transform( to_neg_d );
            REQUIRE( f == old_f.map( to_neg_d ) );
        }
    }

    SECTION( "Using a constant substitution" )
    {
        const auto d = literal{ store.make() };

        const auto to_d = [=]( literal lit )
        {
            return lit.substitute( d.var() );
        };

        f.transform( to_d );
        REQUIRE( f == old_f.map( to_d ) );
    }

    SECTION( "Using a non-constant substitution" )
    {
        const auto aa = literal{ store.make() };
        const auto bb = literal{ store.make() };
        const auto cc = literal{ store.make() };

        const auto g = [=]( literal lit )
        {
            return lit.substitute( lit.var() == a.var() ? aa.var() : lit.var() == b.var() ? bb.var() : cc.var() );
        };

        f.transform( g );
        REQUIRE( f == old_f.map( g ) );
    }

    SECTION( "With literal negation" )
    {
        const auto neg = []( literal lit )
        {
            return !lit;
        };

        f.transform( neg );
        REQUIRE( f == old_f.map( neg ) );
    }
}

TEST_CASE( "Formulas are activated correctly" )
{
    auto store = variable_store{};
    auto f = cnf_formula{};

    const auto a = literal{ store.make() };
    const auto b = literal{ store.make() };
    const auto c = literal{ store.make() };

    f.add_clause( a, b, b );
    f.add_clause( !b, a, c );
    f.add_clause( !c, c );

    REQUIRE( f.literals() == std::vector{ a, b, b, literal::separator, !b, a, c, literal::separator,
        !c, c, literal::separator } );

    const auto d = literal{ store.make() };

    SECTION( "Without an empty clause" )
    {
        REQUIRE( f.activate( d.var() ).literals() == std::vector{ a, b, b, !d, literal::separator, !b, a, c, !d,
            literal::separator, !c, c, !d, literal::separator } );
    }

    SECTION( "With an empty clause" )
    {
        f.add_clause( {} );

        REQUIRE( f.activate( d.var() ).literals() == std::vector{ a, b, b, !d, literal::separator, !b, a, c, !d,
            literal::separator, !c, c, !d, literal::separator, !d, literal::separator } );
    }

    SECTION( "Without any clauses" )
    {
        const auto empty = cnf_formula{};

        REQUIRE( empty.activate( d.var() ).literals().empty() );
    }
}

TEST_CASE( "Constant formulas are constant" )
{
    SECTION( "Tautology" )
    {
        REQUIRE( cnf_formula::constant( true ).literals().empty() );
    }

    SECTION( "Contradiction" )
    {
        REQUIRE( cnf_formula::constant( false ).literals() == std::vector{ literal::separator } );
    }
}

TEST_CASE( "Cube literals comparator orders correctly" )
{
    auto store = variable_store{};

    const auto l1 = literal{ store.make() };
    const auto l2 = literal{ store.make()  };
    const auto l3 = literal{ store.make()  };

    REQUIRE( cube_literal_lt( l1, l2 ) );
    REQUIRE( cube_literal_lt( l2, l3 ) );
    REQUIRE( cube_literal_lt( l1, l3 ) );

    REQUIRE( cube_literal_lt( !l1, l2 ) );
    REQUIRE( cube_literal_lt( l1, !l2 ) );
    REQUIRE( cube_literal_lt( !l1, !l3 ) );

    REQUIRE( cube_literal_lt( !l1, l1 ) );
    REQUIRE( cube_literal_lt( !l2, l2 ) );
    REQUIRE( cube_literal_lt( !l3, l3 ) );

    REQUIRE( !cube_literal_lt( l1, l1 ) );
    REQUIRE( !cube_literal_lt( l2, l1 ) );
    REQUIRE( !cube_literal_lt( l2, l2 ) );
    REQUIRE( !cube_literal_lt( l3, l1 ) );
    REQUIRE( !cube_literal_lt( l3, l2 ) );
    REQUIRE( !cube_literal_lt( l3, l2 ) );

    REQUIRE( !cube_literal_lt( !l1, !l1 ) );
    REQUIRE( !cube_literal_lt( !l2, !l2 ) );
    REQUIRE( !cube_literal_lt( !l3, !l3 ) );

    REQUIRE( !cube_literal_lt( !l2, l1 ) );
    REQUIRE( !cube_literal_lt( l2, !l1 ) );
    REQUIRE( !cube_literal_lt( !l3, l1 ) );
    REQUIRE( !cube_literal_lt( l3, !l1 ) );
}

TEST_CASE( "Cube construction works" )
{
    auto store = variable_store{};

    const auto x = literal{ store.make() };
    const auto y = literal{ store.make() };
    const auto z = literal{ store.make() };

    SECTION( "From an empty vector" )
    {
        REQUIRE( cube{ {} }.literals().empty() );
    }

    SECTION( "From a nonempty vector" )
    {
        using std::ranges::is_permutation;

        REQUIRE( is_permutation( cube{ { x, z } }.literals(),
                 std::vector{ x, z } ) );
        REQUIRE( is_permutation( cube{ { !x, z } }.literals(),
                 std::vector{ !x, z } ) );
        REQUIRE( is_permutation( cube{ { x, y, z } }.literals(),
                 std::vector{ x, y, z } ) );
        REQUIRE( is_permutation( cube{ { x, !y, z } }.literals(),
                 std::vector{ x, !y, z } ) );
        REQUIRE( is_permutation( cube{ { !x, !y, !z } }.literals(),
                 std::vector{ !x, !y, !z } ) );
        REQUIRE( is_permutation( cube{ { x, !x, !y, !z } }.literals(),
                 std::vector{ x, !x, !y, !z } ) );
    }
}

TEST_CASE( "Cube negation works" )
{
    SECTION( "Empty cube" )
    {
        REQUIRE( cube{ {} }.negate().literals() == std::vector{ literal::separator } );
    }

    SECTION( "Non-empty cube" )
    {
        auto store = variable_store{};

        const auto a = literal{ store.make() };
        const auto b = literal{ store.make() };
        const auto c = literal{ store.make() };

        using std::ranges::is_permutation;

        REQUIRE( cube{ { a } }.negate().literals()
                 == std::vector{ !a, literal::separator } );
        REQUIRE( cube{ { !a } }.negate().literals()
                 == std::vector{ a, literal::separator } );
        REQUIRE( is_permutation( cube{ { a, !b, c } }.negate().literals(),
                 std::vector{ !a, b, !c, literal::separator } ) );
        REQUIRE( is_permutation(cube{ { !a, !b, c } }.negate().literals(),
                 std::vector{ a, b, !c, literal::separator } ) );
        REQUIRE( is_permutation(cube{ { a, b, c } }.negate().literals(),
                 std::vector{ !a, !b, !c, literal::separator } ) );
        REQUIRE( is_permutation(cube{ { !a, !b, !c } }.negate().literals(),
                 std::vector{ a, b, c, literal::separator } ) );
        REQUIRE( is_permutation(cube{ { a, !a, !b, !c } }.negate().literals(),
                 std::vector{ a, !a, b, c, literal::separator } ) );
    }
}

TEST_CASE( "Cube subsumption works" )
{
    auto store = variable_store{};
    auto vars = std::vector< literal >{};

    for ( int i = 0; i < 10; ++i )
        vars.emplace_back( store.make() );

    const auto c0 = cube{};
    const auto c1 = cube{ std::vector{ vars[ 0 ], vars[ 1 ], vars[ 2 ] } };
    const auto c2 = cube{ std::vector{ !vars[ 0 ], vars[ 1 ], !vars[ 2 ] } };
    const auto c3 = cube{ std::vector{ vars[ 0 ], vars[ 1 ], vars[ 2 ], vars[ 7 ] } };
    const auto c4 = cube{ std::vector{ vars[ 1 ] } };
    const auto c5 = cube{ std::vector{ !vars[ 1 ] } };
    const auto c6 = cube{ std::vector{ vars[ 8 ], vars[ 7 ], vars[ 6 ], vars[ 2 ], vars[ 1 ], vars[ 0 ], !vars[ 9 ] } };
    const auto c7 = cube{ std::vector{ !vars[ 1 ], vars[ 1 ] } };

    REQUIRE( c0.subsumes( c0 ) );
    REQUIRE( c0.subsumes( c1 ) );
    REQUIRE( c1.subsumes( c1 ) );
    REQUIRE( !c1.subsumes( c4 ) );
    REQUIRE( !c1.subsumes( c5 ) );
    REQUIRE( c1.subsumes( c3 ) );
    REQUIRE( c1.subsumes( c6 ) );
    REQUIRE( c2.subsumes( c2 ) );
    REQUIRE( !c2.subsumes( c4 ) );
    REQUIRE( !c2.subsumes( c1 ) );
    REQUIRE( !c3.subsumes( c1 ) );
    REQUIRE( c3.subsumes( c6 ) );
    REQUIRE( !c4.subsumes( c5 ) );
    REQUIRE( c4.subsumes( c6 ) );
    REQUIRE( c4.subsumes( c7 ) );
    REQUIRE( !c5.subsumes( c4 ) );
    REQUIRE( c5.subsumes( c7 ) );
    REQUIRE( !c6.subsumes( c3 ) );
    REQUIRE( !c6.subsumes( c1 ) );
}

TEST_CASE( "Literals are correctly found in ordered cubes" )
{
    auto store = variable_store{};

    const auto v1 = store.make();
    const auto v2 = store.make();
    const auto v3 = store.make();

    const auto x = literal{ v1 };
    const auto y = literal{ v2 };
    const auto z = literal{ v3 };

    SECTION( "Empty cube" )
    {
        const auto c = cube{ {} };

        REQUIRE( !c.contains( x ) );
        REQUIRE( !c.contains( y ) );
        REQUIRE( !c.contains( z ) );
        REQUIRE( !c.contains( !x ) );
        REQUIRE( !c.contains( !y ) );
        REQUIRE( !c.contains( !z ) );

        REQUIRE( !c.find( v1 ).has_value() );
        REQUIRE( !c.find( v2 ).has_value() );
        REQUIRE( !c.find( v3 ).has_value() );
    }

    SECTION( "Single positive literal" )
    {
        const auto c = cube{ { y } };

        REQUIRE( !c.contains( x ) );
        REQUIRE( c.contains( y ) );
        REQUIRE( !c.contains( z ) );
        REQUIRE( !c.contains( !x ) );
        REQUIRE( !c.contains( !y ) );
        REQUIRE( !c.contains( !z ) );

        REQUIRE( !c.find( v1 ).has_value() );
        REQUIRE( c.find( v2 ).has_value() );
        REQUIRE( *c.find( v2 ) == y );
        REQUIRE( !c.find( v3 ).has_value() );
    }

    SECTION( "Single negative literal" )
    {
        const auto c = cube{ { !y } };

        REQUIRE( !c.contains( x ) );
        REQUIRE( !c.contains( y ) );
        REQUIRE( !c.contains( z ) );
        REQUIRE( !c.contains( !x ) );
        REQUIRE( c.contains( !y ) );
        REQUIRE( !c.contains( !z ) );

        REQUIRE( !c.find( v1 ).has_value() );
        REQUIRE( c.find( v2 ).has_value() );
        REQUIRE( *c.find( v2 ) == !y );
        REQUIRE( !c.find( v3 ).has_value() );
    }

    SECTION( "Two literals, in order" )
    {
        const auto c = cube{ { x, z } };

        REQUIRE( c.contains( x ) );
        REQUIRE( !c.contains( y ) );
        REQUIRE( c.contains( z ) );
        REQUIRE( !c.contains( !x ) );
        REQUIRE( !c.contains( !y ) );
        REQUIRE( !c.contains( !z ) );

        REQUIRE( c.find( v1 ).has_value() );
        REQUIRE( *c.find( v1 ) == x );
        REQUIRE( !c.find( v2 ).has_value() );
        REQUIRE( c.find( v3 ).has_value() );
        REQUIRE( *c.find( v3 ) == z );
    }

    SECTION( "Two literals, out of order" )
    {
        const auto c = cube{ { z, x } };

        REQUIRE( c.contains( x ) );
        REQUIRE( !c.contains( y ) );
        REQUIRE( c.contains( z ) );
        REQUIRE( !c.contains( !x ) );
        REQUIRE( !c.contains( !y ) );
        REQUIRE( !c.contains( !z ) );

        REQUIRE( c.find( v1 ).has_value() );
        REQUIRE( *c.find( v1 ) == x );
        REQUIRE( !c.find( v2 ).has_value() );
        REQUIRE( c.find( v3 ).has_value() );
        REQUIRE( *c.find( v3 ) == z );
    }

    SECTION( "Three literals, all positive" )
    {
        const auto c = cube{ { x, y, z } };

        REQUIRE( c.contains( x ) );
        REQUIRE( c.contains( y ) );
        REQUIRE( c.contains( z ) );
        REQUIRE( !c.contains( !x ) );
        REQUIRE( !c.contains( !y ) );
        REQUIRE( !c.contains( !z ) );

        REQUIRE( c.find( v1 ).has_value() );
        REQUIRE( *c.find( v1 ) == x );
        REQUIRE( c.find( v2 ).has_value() );
        REQUIRE( *c.find( v2 ) == y );
        REQUIRE( c.find( v3 ).has_value() );
        REQUIRE( *c.find( v3 ) == z );
    }

    SECTION( "Three literals, all negative" )
    {
        const auto c = cube{ { !x, !y, !z } };

        REQUIRE( !c.contains( x ) );
        REQUIRE( !c.contains( y ) );
        REQUIRE( !c.contains( z ) );
        REQUIRE( c.contains( !x ) );
        REQUIRE( c.contains( !y ) );
        REQUIRE( c.contains( !z ) );

        REQUIRE( c.find( v1 ).has_value() );
        REQUIRE( *c.find( v1 ) == !x );
        REQUIRE( c.find( v2 ).has_value() );
        REQUIRE( *c.find( v2 ) == !y );
        REQUIRE( c.find( v3 ).has_value() );
        REQUIRE( *c.find( v3 ) == !z );
    }

    SECTION( "Three literals, mixed 1" )
    {
        const auto c = cube{ { !x, y, !z } };

        REQUIRE( !c.contains( x ) );
        REQUIRE( c.contains( y ) );
        REQUIRE( !c.contains( z ) );
        REQUIRE( c.contains( !x ) );
        REQUIRE( !c.contains( !y ) );
        REQUIRE( c.contains( !z ) );

        REQUIRE( c.find( v1 ).has_value() );
        REQUIRE( *c.find( v1 ) == !x );
        REQUIRE( c.find( v2 ).has_value() );
        REQUIRE( *c.find( v2 ) == y );
        REQUIRE( c.find( v3 ).has_value() );
        REQUIRE( *c.find( v3 ) == !z );
    }

    SECTION( "Three literals, mixed 2" )
    {
        const auto c = cube{ { x, y, !z } };

        REQUIRE( c.contains( x ) );
        REQUIRE( c.contains( y ) );
        REQUIRE( !c.contains( z ) );
        REQUIRE( !c.contains( !x ) );
        REQUIRE( !c.contains( !y ) );
        REQUIRE( c.contains( !z ) );

        REQUIRE( c.find( v1 ).has_value() );
        REQUIRE( *c.find( v1 ) == x );
        REQUIRE( c.find( v2 ).has_value() );
        REQUIRE( *c.find( v2 ) == y );
        REQUIRE( c.find( v3 ).has_value() );
        REQUIRE( *c.find( v3 ) == !z );
    }

    SECTION( "Contains only, literals of mixed polarity" )
    {
        const auto c = cube{ { x, y, !z, z } };

        REQUIRE( c.contains( x ) );
        REQUIRE( c.contains( y ) );
        REQUIRE( c.contains( z ) );
        REQUIRE( !c.contains( !x ) );
        REQUIRE( !c.contains( !y ) );
        REQUIRE( c.contains( !z ) );
    }
}
