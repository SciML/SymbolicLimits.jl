using SciMLTesting, SymbolicLimits, Test
using JET

run_qa(
    SymbolicLimits;
    explicit_imports = true,
    ei_kwargs = (;
        # Non-public names from SymbolicUtils / Base.Iterators accessed qualified;
        # they go public as those base libs declare them public.
        all_qualified_accesses_are_public = (;
            ignore = (
                :ShapeVecT, :Sym, :_iszero,   # SymbolicUtils
                :peel,                         # Base.Iterators
            ),
        ),
        # Non-public names explicitly imported from SymbolicUtils.
        all_explicit_imports_are_public = (;
            ignore = (
                :BasicSymbolic, :isadd, :isaddmul, :isconst, :isdiv,
                :ismul, :issym, :isterm, :symtype,   # SymbolicUtils
            ),
        ),
    ),
)
