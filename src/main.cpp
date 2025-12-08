#include "aiger.h"
#include "logic.hpp"
#include "logger.hpp"
#include "aiger_builder.hpp"
#include <print>
#include <string>
#include <optional>
#include <memory>

static constexpr const char* help_content =
    "Usage: pdrtpa [-v | --verbose] [-d | --debug] <input.aig>";

using aiger_ptr = std::unique_ptr< aiger, decltype( &aiger_reset ) >;

static aiger_ptr make_aiger()
{
    return { aiger_init(), &aiger_reset };
}

int main( int argc, char** argv )
{
    auto verbosity = verbosity_level::silent;
    auto input_path = std::optional< std::string >{};

    for ( int i = 1; i < argc; ++i )
    {
        const auto arg = std::string{ argv[i] };

        if ( arg.starts_with( '-' ) )
        {
            if ( arg == "-v" || arg == "--verbose" )
                verbosity = verbosity_level::loud;
            else if ( arg == "-d" || arg == "--debug" )
                verbosity = verbosity_level::debug;
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
}
