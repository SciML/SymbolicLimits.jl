module SymbolicLimits

module Internals
    include("limits.jl")
end

using .Internals: limit
export limit

end
