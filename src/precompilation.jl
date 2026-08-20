@setup_workload begin
    @syms x::Real
    finite_expr = x + 1
    reciprocal_expr = 1 / x
    positive_inf_expr = x^2 / exp(x)
    negative_inf_expr = x * exp(x)

    @compile_workload begin
        limit(finite_expr, x, 0)
        limit(reciprocal_expr, x, 0, :left)
        limit(reciprocal_expr, x, 0, :right)
        limit(positive_inf_expr, x, Inf)
        limit(negative_inf_expr, x, -Inf)
    end
end
