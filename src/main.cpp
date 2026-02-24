#include "aiger.hpp"
#include "logic.hpp"
#include "transition_system.hpp"
#include "logger.hpp"
#include "aiger_builder.hpp"
#include "verifier.hpp"
#include "simplifier.hpp"
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

}

int main( int argc, char** argv ) // NOLINT: Don't care about bad_alloc's here.
{
    auto verbosity = verbosity_level::silent;
    auto input_path = std::optional< std::string >{};
    auto generalization_preference = generalization_preference::right; // TODO: Choose a default.

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
            else if ( arg == "--left" )
            {
                generalization_preference = generalization_preference::left;
            }
            else if ( arg == "--right" )
            {
                generalization_preference = generalization_preference::right;
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

    logger::log_line_loud( "Generalization preference: {}",
        generalization_preference == generalization_preference::left ? "left" : "right" );
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

    logger::log_loud( "Simplifying... " );

    auto simplified_system = simplify( *system );

    logger::log_line_loud( "OK" );
    logger::log_line_loud( "Running..." );
    logger::log_debug( "\n" );

    auto engine = verifier{ store, simplified_system, generalization_preference };
    const auto result = engine.run();

    logger::log_debug( "\n" );
    logger::log_line_loud( "Finished" );
    logger::log_line_loud( "Printing the witness to stdout...\n" );

    std::print( "{}", format_witness( *system, result ) );

    return 0;
}
