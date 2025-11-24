#include "common.hpp"
#include "logic.hpp"

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
