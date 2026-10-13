# GeoDa Lean: formalizing the GNS nesting of spatial econometric models

Lean 4 + Mathlib formalization of the equation-level nesting of the General
Nesting Spatial (GNS) model into SAR, SEM and SDM, together with the reduced
forms of SAR and SEM under an invertibility assumption.

**Status: compiler-verified.** `./scripts/verify.sh` builds every target, checks
that no proof uses `sorry` or `admit`, and audits the axioms of all 12 main
theorems (see [Verification](#verification) for the exact toolchain, command and
observed output).

## Contents

```
GeoDa.lean             root module
GeoDa/GNS.lean         abstract version: W is an arbitrary ℝ-linear endomorphism
GeoDa/Weights.lean     concrete version: W is a real n×n matrix; reduced forms
GeoDaTest/Smoke.lean   compile-time tests (signature pins, explicit examples)
GeoDaTest/Axioms.lean  axiom audit, driven by scripts/verify.sh
scripts/verify.sh      the verification suite
.github/workflows/     CI running the same suite
```

## What is formalized

### Model equations

With `Vec n := Fin n → ℝ`, GNS is

```
GNS : y = ρWy + Xβ + WXθ + u   ∧   u = λWu + ε
```

and the three classical special cases are obtained by switching coefficients
off:

| model | equation |
| --- | --- |
| `SAR` | `y = ρWy + Xβ + ε` |
| `SEM` | `y = Xβ + u`, `u = λWu + ε` |
| `SDM` | `y = ρWy + Xβ + WXθ + ε` |

### Nesting (`GeoDa.GNS`, `GeoDa.Weights`)

`gns_iff_sar`, `gns_iff_sem`, `gns_iff_sdm` state that GNS with the relevant
coefficients set to zero is *exactly* the corresponding special case. For SAR and
SDM this is an equivalence with `SAR ∧ u = ε` / `SDM ∧ u = ε`: because GNS
carries a latent disturbance `u` while SAR and SDM absorb the error, the two
conventions agree only when `u = ε`, and the theorem says so explicitly rather
than hiding it.

The `…Mat` variants restate the same results for a concrete `n × n` matrix `W`
acting by `Matrix.mulVec`.

### Structural equation versus linear system

`sarMat_iff_mulVec` and `semMat_iff_mulVec` rewrite the structural equations as
linear systems:

* SAR holds iff `(1 - ρW) y = Xβ + ε`;
* SEM holds iff `(1 - λW) u = ε ∧ y = Xβ + u`.

### Reduced forms (`GeoDa.Weights`)

The invertibility hypothesis is `IsUnit (1 - ρ • W)` in the matrix ring; for
square matrices over `ℝ` this is equivalent to nonsingularity.

* `sarMat_iff_reducedForm`: SAR holds iff `y = (1 - ρW)⁻¹ (Xβ + ε)`.
* `semMat_iff_reducedForm`: SEM holds iff `u = (1 - λW)⁻¹ ε` and
  `y = Xβ + (1 - λW)⁻¹ ε`.

### SAR versus SEM

* `sem_reducedForm_eq_sar_reducedForm_of_filtered`: with `B = (1 - λW)⁻¹`, the SEM
  reduced form `Xβ + Bε` equals the SAR reduced form whose regressors have been
  spatially filtered to `(1 - λW)Xβ`. This is the precise sense in which a SEM
  "is" a SAR: not with the same regressors, but with the common-factor-filtered
  ones.
* `reducedForm_eq_iff_inverse_eq_one`: the two reduced forms agree as functions
  of `(Xβ, ε)` — i.e. SAR and SEM are observationally equivalent — exactly when
  the inverse matrices collapse to the identity. So for `ρW ≠ 0` and `λW ≠ 0`
  they are **not** observationally equivalent; the equivalence in the previous
  item is an equivalence *after transforming the regressors*.

## Scope and non-claims

This is a formalization of *model equations*. It does **not** establish
identifiability, estimator consistency, asymptotic distribution theory, or
numerical correctness. It makes no novelty claim about the mathematics: the
nesting results are textbook (Anselin), and the reduced-form statements are
matrix algebra. `W` is an arbitrary real matrix — row standardization, symmetry,
non-negativity and any other regularity of spatial weights are *not* assumed.

The abstract file `GeoDa/GNS.lean` still takes `Xβ` and `WXθ` as supplied vectors
rather than forming them as matrix products; only in `GeoDa/Weights.lean` is `W`
concrete.

## Import policy

The project imports the specific Mathlib modules it needs rather than the whole
of Mathlib. This keeps builds fast and the CI cache small; `import Mathlib` would
pull in all ~8600 Mathlib modules. Note `*ᵥ` is a *scoped* notation, so files
using it need `open scoped Matrix` (and `open Matrix` for the lemma names).

## Verification

Toolchain: Lean `leanprover/lean4:v4.35.0`, Mathlib `v4.35.0`
(`rev 56a005855ea17e0b0958f73ec801ae140b0a1679`); both pinned in `lean-toolchain`
and `lake-manifest.json`.

```
$ ./scripts/verify.sh
==> 1/3  lake build
Build completed successfully (1276 jobs).
==> 2/3  no sorry / admit
     ok: no sorry/admit in any proof
==> 3/3  axiom audit
'GeoDa.gns_iff_sar' depends on axioms: [propext, Classical.choice, Quot.sound]
… (12 theorems, all on the same list)
     ok: all 12 theorems depend only on [propext, Classical.choice, Quot.sound]

VERIFICATION SUCCEEDED
```

Every main theorem depends only on Lean's three standard axioms; none depends on
`sorryAx`, and no additional axiom is introduced.

CI (`.github/workflows/lean.yml`) runs the same suite on GitHub-hosted runners via
`leanprover/lean-action`, which installs the pinned toolchain, fetches the Mathlib
cache and builds.

## Provenance

The initial `GeoDa/GNS.lean` in this repository was written as a draft and had
never been run through the compiler. Fixing it required two substantive changes
beyond cosmetics:

1. the disturbance coefficient was bound as `λ`, which is Lean's lambda token and
   cannot be used as an identifier — every occurrence was renamed to `lam`;
2. `simp` leaves `(P ∧ Q) ↔ (R ∧ Q)` in a form it does not close, and the
   `0 • W u` / `0 + u` terms need explicit handling; the nesting proofs were
   rewritten to be independent of `simp`'s normal form.

The matrix development, the reduced-form and equivalence theorems, the tests and
the CI configuration were added in the same pass. All of it was produced with
Claude (Claude desktop, this session), **not** with Codex: if the milestone
requires the proofs to be Codex's own work, they should be re-derived
independently and the two versions compared.

## Next steps

1. Form `Xβ` and `WXθ` from concrete design matrices instead of taking them as
   given vectors.
2. Prove the reduced forms under the weaker hypothesis `det (1 - ρ • W) ≠ 0`,
   connecting `IsUnit` to `Matrix.isUnit_iff_isUnit_det`.
3. Row-standardized weights: prove `W ⬝ 1 = 1` type properties and the
   invertibility of `1 - ρW` for `|ρ| < 1` (Neumann series / Gershgorin).
4. Numerical cross-checks against PySAL `spreg`.
