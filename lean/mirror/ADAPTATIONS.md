# Adaptations of the vendored mirror (Lean 4.35.0 -> 4.36.0)

Source: see `UPSTREAM`. Policy: adapt only what the toolchain bump requires; never edit theorem statements.

## Files not carried over (replaced by the package-level build config)

| File | Reason |
|---|---|
| `lakefile.lean` | replaced by `../lakefile.toml` (library `K8sMirror`, `srcDir = "mirror"`, same seven roots and `.submodules` globs, `autoImplicit = false` as before) |
| `lean-toolchain` | the pinned cedar-spec decides the toolchain (D-8): `leanprover/lean4:v4.36.0` |
| `lake-manifest.json`, `.gitignore` | regenerated at package level (`../lake-manifest.json`, `../.gitignore`) |

## Source adaptations

None. All 21 `.lean` modules compile unchanged under v4.36.0 (`lake build K8sMirror`: 44 jobs, 0 errors).
The new toolchain emits linter warnings only (e.g. `linter.unusedSimpArgs`), which are left as-is.

## Counts against `STATUS.md`

| Quantity | STATUS.md | Measured here | Note |
|---|---|---|---|
| modules | 23 | 21 `.lean` files | STATUS.md's 23 is not reproducible from the tree; the tree has 21 modules (9 in `authorizer/`, 2 each in the other six directories). The vendored STATUS.md is unchanged; the discrepancy predates this copy (the source tree at 2ee49d340c9 has the same 21 `.lean` modules plus `lakefile.lean`) |
| theorems | 347 | 347 lines matching `^theorem `; 365 when also counting 17 `@[simp] theorem` and 1 `private theorem` | STATUS.md counts only column-0 `theorem` |
| `sorry` | 0 | 0 | |
| axioms | 2 (both in `cel/`) | 2 `axiom` declarations (`oAuthor`, `P_76_O3_builtin_agrees_with_author`) | unchanged |
