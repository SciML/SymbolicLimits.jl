using SafeTestsets

@safetestset "Code quality (Aqua.jl)" begin
    using SymbolicLimits
    using Aqua
    Aqua.test_all(SymbolicLimits, deps_compat = false, ambiguities = false)
    Aqua.test_deps_compat(SymbolicLimits, check_extras = false)
end

@safetestset "Static analysis (JET.jl)" begin
    using JET
    JET.report_package("SymbolicLimits"; target_defined_modules = true)
end
