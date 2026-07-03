using SciMLTesting, SymbolicLimits, Test
using JET

run_qa(
    SymbolicLimits;
    explicit_imports = true,
    ei_kwargs = (;
        # Non-public names from SymbolicUtils accessed qualified;
        # they go public as SymbolicUtils declares them public.
        all_qualified_accesses_are_public = (;
            ignore = (
                :ShapeVecT, :_iszero,   # SymbolicUtils
            ),
        ),
        # Non-public names explicitly imported from SymbolicUtils.
        all_explicit_imports_are_public = (;
            ignore = (
                :isaddmul, :isconst,   # SymbolicUtils
            ),
        ),
    ),
)
