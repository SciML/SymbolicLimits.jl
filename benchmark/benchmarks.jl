using SymbolicLimits, SymbolicUtils, BenchmarkTools

const SUITE = BenchmarkGroup()

@syms x::Real ω::Real

# =============================================================================
# Limits (Gruntz algorithm)
# =============================================================================

SUITE["limit"] = BenchmarkGroup()

SUITE["limit"]["reciprocal"] = @benchmarkable limit(-1 / $x, $x, Inf)
SUITE["limit"]["log_ratio"] = @benchmarkable limit(-$x / log($x), $x, Inf)
SUITE["limit"]["exp_nested"] = @benchmarkable limit(
    exp($x + exp(-$x)) - exp($x), $x, Inf
)
SUITE["limit"]["poly_over_exp"] = @benchmarkable limit($x^7 / exp($x), $x, Inf)
SUITE["limit"]["poly_log"] = @benchmarkable limit(
    $x^2 / ($x^2 + log($x)), $x, Inf
)
SUITE["limit"]["neg_inf"] = @benchmarkable limit($x * exp($x), $x, -Inf)

# =============================================================================
# Internal engine pieces
# =============================================================================

SUITE["engine"] = BenchmarkGroup()

SUITE["engine"]["zero_equivalence"] = @benchmarkable SymbolicLimits.zero_equivalence(
    $x * ($x + 2) - $x - 2 * $x + $x - $x * ($x + 1) + $x, Set{Any}()
)
SUITE["engine"]["series_term"] = @benchmarkable SymbolicLimits.get_series_term(
    log(exp($x)), $x, nothing, 2, Set{Any}()
)
SUITE["engine"]["leading_exponent"] = @benchmarkable SymbolicLimits.get_leading_exponent(
    $x^2, $x, nothing, Set{Any}()
)
