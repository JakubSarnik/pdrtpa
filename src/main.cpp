#include "aiger.hpp"
#include "logic.hpp"
#include "transition_system.hpp"
#include "logger.hpp"
#include "aiger_builder.hpp"
#include "verifier.hpp"
#include <print>
#include <string>
#include <optional>
#include <memory>
#include <concepts>
#include <random>
#include <charconv>

namespace
{

constexpr const char* help_content =
    "Usage: pdrtpa [-v | --verbose] [-d | --debug] <input.aig>";

std::string format_witness( const transition_system& sys, const verifier::result_t& counterexample )
{
    auto row = []< typename T >( const std::vector< T >& literals )
    {
        auto res = std::string{};

        for ( const auto lit : literals )
        {
            if constexpr ( std::same_as< T, literal > )
                res += lit.positive() ? '1' : '0';
            else
                res += lit ? '1' : '0';
        }

        res += "\n";

        return res;
    };

    if ( !counterexample.has_value() )
        return "0\nb0\n.\n";

    auto witness = std::string( "1\nb0\n" );

    witness += row( sys.initial_cube() );

    for ( const auto& in : *counterexample )
        witness += row( in );

    witness += ".\n";

    return witness;
}

unsigned int get_seed( const std::optional< std::string >& seed_string )
{
    if ( seed_string.has_value() )
    {
        auto view = std::string_view{ *seed_string };
        constexpr auto prefix = std::string_view{ "-s" };

        assert( view.starts_with( prefix ) );
        view.remove_prefix( prefix.size() );

        const auto last = view.data() + view.size(); // NOLINT: Pointer arithmetic needed by the API.
        unsigned int result = 0;

        // NOLINTNEXTLINE: We do not care about null termination here at all.
        const auto [ ptr, ec ] = std::from_chars( view.data(), last, result );

        if ( ec == std::errc{} && ptr == last ) // NOLINT: errc can be value-initialized.
            return result;
    }

    return std::random_device{}();
}

}

int main( int argc, char** argv ) // NOLINT: Don't care about bad_alloc's here.
{
    auto verbosity = verbosity_level::silent;
    auto input_path = std::optional< std::string >{};
    auto seed_string = std::optional< std::string >{};

    for ( int i = 1; i < argc; ++i )
    {
        const auto arg = std::string{ argv[i] }; // NOLINT: Unavoidable

        if ( arg.starts_with( '-' ) )
        {
            if ( arg == "-v" || arg == "--verbose" )
            {
                verbosity = verbosity_level::loud;
            }
            else if ( arg == "-d" || arg == "--debug" )
            {
                verbosity = verbosity_level::debug;
            }
            else if ( arg.starts_with( "-s" ) )
            {
                seed_string = arg;
            }
            else if ( arg == "-h" || arg == "--help" )
            {
                std::println( help_content );
                return 0;
            }
            else
            {
                std::println( "Error: unsupported option: {}", arg );
                std::println( help_content );
                return 1;
            }
        }
        else
        {
            input_path = arg;
        }
    }

    if ( !input_path )
    {
        std::println( "Error: no input file specified" );
        std::println( help_content );
        return 1;
    }

    logger::set_verbosity( verbosity );

    const auto seed = get_seed( seed_string );

    logger::log_line_loud( "Randomness seed: {}", seed );
    logger::log_loud( "Loading aig from file... " );

    auto aig = make_aiger();
    const char* msg = aiger_open_and_read_from_file( aig.get(), input_path->c_str() );

    if ( msg != nullptr )
    {
        std::println( "\nError: {}", msg );
        return 1;
    }

    logger::log_line_loud( "OK" );
    logger::log_loud( "Building the transition system... " );

    auto store = variable_store{};
    auto system = builder::build_from_aiger( store, *aig );

    if ( !system.has_value() )
    {
        std::println( "\nError: {}", system.error() );
        return 1;
    }

    logger::log_line_loud( "OK" );
    logger::log_line_debug( "\tAiger latches:   {}", aig->num_latches );
    logger::log_line_debug( "\tState variables: {}", system->state_vars().size() );

    // TODO: At this point, we could simplify the three formulae, each in its
    //       own solver and using cadical's freeze on state, next state and
    //       input vars, then calling simplify and finally traversing the
    //       clauses again (ClauseIterator) to get the simplified formulae. Is
    //       this good or not? Investigate once the model checker itself is
    //       implemented.

    logger::log_line_loud( "Running..." );
    logger::log_debug( "\n" );

    auto engine = verifier{ store, *system, seed };
    const auto result = engine.run();

    logger::log_debug( "\n" );
    logger::log_line_loud( "Finished" );
    logger::log_line_loud( "Printing the witness to stdout...\n" );

    std::print( "{}", format_witness( *system, result ) );

    return 0;
}
