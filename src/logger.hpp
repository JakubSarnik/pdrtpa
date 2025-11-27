#pragma once

#include <format>
#include <print>

enum class verbosity_level
{
    silent,
    loud,
    debug
};

class logger
{
    inline static verbosity_level verbosity = verbosity_level::silent;

public:
    logger() = delete;

    static void set_verbosity( verbosity_level new_verbosity )
    {
        verbosity = new_verbosity;
    }

    template< class... Args >
    static void log( verbosity_level min, std::format_string<Args...> fmt, Args&&... args )
    {
        if ( verbosity >= min )
            std::print( fmt, std::forward< Args >( args )... );
    }

    template< class... Args >
    static void log_loud( std::format_string<Args...> fmt, Args&&... args )
    {
        log( verbosity_level::loud, fmt, std::forward< Args >( args )... );
    }

    template< class... Args >
    static void log_debug( std::format_string<Args...> fmt, Args&&... args )
    {
        log( verbosity_level::debug, fmt, std::forward< Args >( args )... );
    }

    template< class... Args >
    static void log_line( verbosity_level min, std::format_string<Args...> fmt, Args&&... args )
    {
        if ( verbosity >= min )
            std::println( fmt, std::forward< Args >( args )... );
    }

    template< class... Args >
    static void log_line_loud( std::format_string<Args...> fmt, Args&&... args )
    {
        log_line( verbosity_level::loud, fmt, std::forward< Args >( args )... );
    }

    template< class... Args >
    static void log_line_debug( std::format_string<Args...> fmt, Args&&... args )
    {
        log_line( verbosity_level::debug, fmt, std::forward< Args >( args )... );
    }
};
