#pragma once

#include "logic.hpp"
#include "transition_system.hpp"
#include <vector>
#include <optional>

class verifier
{
public:
    using result_t = std::optional< std::vector< std::vector< literal > > >;

    [[nodiscard]] result_t run( const transition_system& system );
};
