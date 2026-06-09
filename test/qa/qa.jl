using SymbolicLimits
using Test
using Aqua
using JET

@testset "Code quality (Aqua.jl)" begin
    Aqua.test_all(SymbolicLimits, deps_compat = false, ambiguities = false)
    Aqua.test_deps_compat(SymbolicLimits, check_extras = false)
end

@testset "Static analysis (JET.jl)" begin
    JET.report_package("SymbolicLimits"; target_defined_modules = true)
end
