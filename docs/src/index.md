```@meta
CurrentModule = SymbolicLimits
```

# SymbolicLimits.jl

SymbolicLimits.jl is a Julia package for computing symbolic limits using the Gruntz algorithm. It provides robust limit computation for complex symbolic expressions involving exponentials, logarithms, and algebraic operations.

## Overview

Computing symbolic limits is a fundamental operation in symbolic mathematics, but it's also computationally challenging. Zero equivalence of log-exp functions is undecidable and reducible to computing symbolic limits. SymbolicLimits.jl implements the Gruntz algorithm to handle this complexity by using a heuristic zero-equivalence detector and tracking all assumptions made during computation.

## Key Features

- **Robust Limit Computation**: Handles complex expressions involving exponentials and logarithms
- **Assumption Tracking**: Returns both the limit result and the assumptions required for correctness
- **Gruntz Algorithm**: Implements the state-of-the-art algorithm for symbolic limits
- **Direction Support**: Supports left-sided, right-sided, and two-sided limits

## Quick Start

```julia
using SymbolicLimits, SymbolicUtils

@syms x::Real

# Basic limits
limit(exp(x+exp(-x))-exp(x), x, Inf)
limit(-1/x, x, Inf)
limit(-x / log(x), x, Inf)
```

## Limitations and Assumptions

Since zero equivalence is undecidable, SymbolicLimits uses heuristics and tracks assumptions. The returned result is correct if all tracked assumptions hold. In practice, the heuristics are reliable for most mathematical expressions encountered in typical use cases.

## Algorithm Background

The package implements the Gruntz algorithm (1996), which handles limits by:

1. Finding most rapidly varying subexpressions (MRV sets)
2. Rewriting expressions in terms of distinguished subexpressions
3. Computing series expansions around the most varying terms
4. Extracting leading coefficients and exponents

## Optional GruntzLimit.jl backend

Loading [GruntzLimit.jl](https://github.com/jverzani/GruntzLimit.jl) (MIT, by jverzani and
contributors) with `using GruntzLimit` activates a package extension. [`limit`](@ref) then runs
the algorithm of this package first. Only when it does not produce a result is GruntzLimit
consulted, which handles trigonometric, hyperbolic, inverse and special functions, non-integer
powers and symbolic limit points. The returned assumptions set is empty when GruntzLimit's
answer does not depend on generic assumptions about symbolic parameters. When GruntzLimit
proves that the limit does not exist, `limit` throws an `ArgumentError`. The extension
declines inputs where a generic GruntzLimit answer would depend on such assumptions (for
example `sin(x) / (a + x)`, whose limit is 1 when `a` is 0), inputs containing a numeric
constant other than `Float64`, and symbolic leaves named `π` or `ℯ`; the error of this
package's algorithm is then thrown.

```julia
using SymbolicLimits, SymbolicUtils, GruntzLimit

@syms x::Real
limit(sin(x) / x, x, 0)
```

## API Reference

```@docs
limit
```
