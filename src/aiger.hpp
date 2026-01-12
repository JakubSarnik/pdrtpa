#pragma once

#include "aiger.h"
#include <memory>

using aiger_ptr = std::unique_ptr< aiger, decltype( &aiger_reset ) >;

inline aiger_ptr make_aiger()
{
    return { aiger_init(), &aiger_reset };
}