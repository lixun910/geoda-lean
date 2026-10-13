# GeoDa Lean: formalizing the GNS nesting of spatial econometric models

Lean 4 + Mathlib formalization of the equation-level nesting of the General
Nesting Spatial (GNS) model into SAR, SEM and SDM, together with the full GNS
reduced form and the SAR/SEM/SDM reduced forms under an invertibility
assumption, and the spatial weights predicates (nonnegativity, row
standardization, islands) those models are stated over.

**Status: compiler-verified.** `./scripts/verify.sh` builds every target, checks
that no proof uses `sorry` or `admit`, and audits the axioms of all 82 main
theorems (see [Verification](#verification) for the exact toolchain, command and
observed output).

## Contents

```
GeoDa.lean                root module
GeoDa/GNS.lean            abstract version: W is an arbitrary ℝ-linear endomorphism
GeoDa/Weights.lean        concrete version: W is a real n×n matrix; reduced forms
GeoDa/Design.lean         design matrix X; Xβ and WXθ formed by matrix product
GeoDa/ReducedForm.lean    the full GNS reduced form, eliminating u and y together
GeoDa/Multiplier.lean     invertibility of 1 - ρW from the weights themselves
GeoDa/RandomVector.lean   probability layer: expectation, covariance, model moments
GeoDa/SpatialWeights.lean weights predicates, row normalization, islands
GeoDaTest/Smoke.lean      compile-time tests (signature pins, explicit examples)
GeoDaTest/Axioms.lean     axiom audit, driven by scripts/verify.sh
scripts/verify.sh         the verification suite
validation/               numerical cross-checks against NumPy, SciPy and PySAL spreg
.github/workflows/        CI: the verification suite, and the numerical cross-checks
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

### Design matrix (`GeoDa.Design`)

`GeoDa.GNS` and `GeoDa.Weights` take `Xβ` and `WXθ` as *supplied vectors*: the
arguments `xb` and `wxθ` are named after those terms, but nothing in those files
multiplies a design matrix by a parameter vector to produce them. `GeoDa.Design`
closes that gap. With a design matrix and two coefficient vectors

```
X : Matrix (Fin n) (Fin k) ℝ        β θ : Fin k → ℝ
```

the four equations are restated with `Xβ := X *ᵥ β` and `WXθ := (W * X) *ᵥ θ`:

| model | Lean name |
| --- | --- |
| GNS | `GNSDes` |
| SAR | `SARDes` |
| SEM | `SEMDes` |
| SDM | `SDMDes` |

The results are:

* `design_wxθ_eq`: `W *ᵥ (X *ᵥ θ) = (W * X) *ᵥ θ` — the lagged-regressor term is the
  expected one, `W` applied to the fitted values `Xθ`;
* `gnsDes_iff_gnsMat`, `sarDes_iff_sarMat`, `semDes_iff_semMat`, `sdmDes_iff_sdmMat`:
  each design-matrix equation *is* the corresponding `GeoDa.Weights` equation with
  `xb := X *ᵥ β` and `wxθ := (W * X) *ᵥ θ`, so nothing is lost or added by replacing
  the supplied vectors with products;
* `gnsDes_iff_sarDes`, `gnsDes_iff_semDes`, `gnsDes_iff_sdmDes`: the nesting results,
  with the same explicit `u = ε` convention for SAR and SDM;
* `sarDes_iff_mulVec`, `semDes_iff_mulVec`: the linear-system form;
* `sarDes_iff_reducedForm`, `semDes_iff_reducedForm`: the reduced forms;
* `semDes_reducedForm_eq_sarDes_reducedForm_of_filtered`: the SEM/SAR
  filtered-regressor equivalence.

The design matrix `X` is arbitrary: no full-rank, centring or intercept-column
assumption is made, and `k` need not be related to `n`.

### The full GNS reduced form (`GeoDa.ReducedForm`)

`GeoDa.Design` proves the SAR and SEM reduced forms *separately* — one equation
at a time. `GeoDa.ReducedForm` eliminates **both** latent quantities of GNS at
once. With

```
A = 1 - ρW        B = 1 - λW
```

both invertible, the GNS system

```
y = ρWy + Xβ + WXθ + u        u = λWu + ε
```

is *equivalent* to

```
u = B⁻¹ ε
y = A⁻¹ (Xβ + WXθ + B⁻¹ ε)
```

* `gnsDes_iff_reducedForm_of_inverse` : the workhorse, taking explicit two-sided
  inverses `A` and `B` rather than `IsUnit` data.
* `gnsDes_iff_reducedForm` : the `IsUnit` form, matching the convention of
  `GeoDa.Weights`.
* `gnsDes_iff_reducedForm_of_det_ne_zero` : the form an implementation actually
  checks, `det (1 - ρW) ≠ 0` and `det (1 - λW) ≠ 0`, via
  `isUnit_iff_det_ne_zero`.
* `gnsDes_reducedForm` and `reducedForm_gnsDes` : the two implications named
  separately. The reverse one is the substantive half: it says the reduced form
  has neither dropped a solution nor introduced one, which is what licenses
  treating it as *the* model.
* `gnsDes_iff_mulVec` : GNS is a pair of linear systems,
  `(1 - ρW)y = Xβ + WXθ + u` and `(1 - λW)u = ε`, both equations kept.
* `sdmDes_iff_mulVec`, `sdmDes_iff_reducedForm` : the SDM restriction. SDM is GNS
  with `λ = 0`, where `B = 1` and `u = ε`, so the reduced form collapses to
  `y = (1 - ρW)⁻¹ (Xβ + WXθ + ε)`. (SAR and SEM are already in `GeoDa.Design`.)

The hypothesis is *stated*, not derived: nothing here shows that `1 - ρW` is
invertible, let alone for `|ρ| < 1`. See the [next steps](#next-steps).

### Spatial weights (`GeoDa.SpatialWeights`)

Everywhere above, `W` is an arbitrary real matrix. Real spatial weights are not
arbitrary, and this file states the regularities as **explicit predicates**
instead of baking them into the definitions:

| predicate | meaning |
| --- | --- |
| `Nonneg W` | every entry is `≥ 0` |
| `RowStochastic W` | every row sums to `1` |
| `RowSubstochastic W` | every row sums to at most `1` |
| `Island W i` | region `i` is a zero row — no neighbours |
| `ZeroDiag W` | no region is its own neighbour |

* `mulVec_one_apply`: `(W *ᵥ 1) i = ∑ j, W i j`, i.e. applying `W` to the
  constant vector sums each row.
* `rowStochastic_iff_mulVec_one`: `W *ᵥ 1 = 1` exactly for row-stochastic `W`.
* `island_iff_rowSum_eq_zero`: for nonnegative `W`, a row is an island exactly
  when its row sum vanishes; `not_rowStochastic_of_island` records that a
  row-stochastic matrix therefore has no islands.
* `normalize` divides each entry of row `i` by `∑ j, W i j`. **Islands are not a
  special case in the code**: `ℝ`'s inverse is totalized by `(0 : ℝ)⁻¹ = 0`, so
  a zero row is carried to a zero row rather than dividing by zero, and
  `island_normalize` states exactly that. Normalization preserves nonnegativity
  and a zero diagonal, and is always row-substochastic
  (`rowSubstochastic_normalize`), with no hypothesis on `W` at all.
* `rowStochastic_normalize_iff` / `rowStochastic_normalize_iff_pos`: for
  nonnegative `W`, the normalized matrix is row-stochastic exactly when `W` has
  no island, equivalently when every row sum is positive.

**Symmetry and a zero diagonal are deliberately not assumed.** A zero diagonal
is independent of row standardization in both directions, and both halves are
proved: the identity is row-stochastic with a nonzero diagonal
(`not_zeroDiag_one`), while `!![0, 1; 0, 0]` has a zero diagonal but a vanishing
row (`GeoDaTest.wnotdiag_not_rowStochastic`).

### Invertibility of the spatial multiplier (`GeoDa.Multiplier`)

Every reduced form above carries an invertibility hypothesis on `1 - ρW` and
`1 - λW`, taken as `IsUnit` or as a nonvanishing determinant. Those are *stated*,
never derived, so on their own they say nothing about which weights satisfy them.
`GeoDa.ReducedForm`'s docstring says as much. `GeoDa.Multiplier` closes that gap
for the weights the models are actually used with.

For **nonnegative row-substochastic** `W` — every entry `≥ 0`, every row summing
to at most `1`, islands included — applying `W` cannot increase the `ℓ∞` norm of a
vector:

* `norm_mulVec_le`: `‖W *ᵥ v‖ ≤ ‖v‖`. Row `i` contributes at most
  `(∑ j, W i j) · ‖v‖ ≤ ‖v‖`, which is the row-sum estimate `‖W‖∞ ≤ 1` of the
  spatial-weights literature, stated on vectors so that no matrix norm is needed.
  `abs_mulVec_apply_le_norm` is the coordinate-wise version.
* `mulVec_injective_one_sub_smul`: for `|ρ| < 1`, `1 - ρW` is injective —
  `(1 - ρW)v = 0` gives `v = ρ • (Wv)`, hence `‖v‖ ≤ |ρ| ‖v‖`, and `|ρ| < 1`
  forces `‖v‖ = 0`.
* `isUnit_one_sub_smul_of_rowSubstochastic`: **`|ρ| < 1` implies
  `IsUnit (1 - ρ • W)`**, with the weights assumptions explicit and no `IsUnit`
  in sight. The same statement is used unchanged for the spatial-error parameter
  `λ`; nothing in the proof is `ρ`-specific.
  `isUnit_one_sub_smul_of_rowStochastic` is the row-stochastic case.
* `sarMat_iff_reducedForm_of_rowSubstochastic` and
  `semMat_iff_reducedForm_of_rowSubstochastic` are the bridges: the SAR and SEM
  reduced forms with `IsUnit` replaced by the weights hypotheses and `|ρ| < 1`.

Two hypotheses are used, and neither is decorative. `GeoDaTest.wtwo_not_isUnit`
shows `2 • 1` — nonnegative, rows summing to `2` — makes the multiplier
`1 - (1/2)·2·1 = 0` at `ρ = 1/2`; `GeoDaTest.wneg_not_isUnit` shows
`!![2, -1; 0, 0]` — row sums `1` and `0`, but a negative entry — makes it the
singular `!![0, 1/2; 0, 1]`. So nonnegativity and row-substochasticity are both
needed, and `|ρ| < 1` alone does not suffice for an arbitrary `W`.

Islands are *allowed*: the island matrix `Wisland` is covered by
`isUnit_one_sub_smul_of_rowSubstochastic` precisely because the hypothesis is
sub-stochasticity, not standardization.

### Probability: randomness only in `ε` (`GeoDa.RandomVector`)

Everything above is deterministic. This file starts the probability layer, and the
separation is kept strict:

* `Ω` is a measurable space with a probability measure `μ`;
* a **random vector** is an ordinary function `ξ : Ω → Vec n`;
* `X`, `W`, `β`, `θ`, `ρ`, `λ` stay deterministic — the *same* objects as
  everywhere else in the repository, never random;
* only `ε`, and the `u` and `y` built from it, are random.

Expectation and covariance are defined coordinatewise,
`(rvExp μ ξ) i = ∫ ω, ξ ω i ∂μ` and
`(rvCov μ ξ) i j = ∫ ω, (ξ i - Eξ i)(ξ j - Eξ j) ∂μ`, which keeps every integral a
real-valued Lebesgue integral: no Bochner integral in a normed space, no
`ContinuousLinearMap` commutation, no matrix norm.

**Integrability is assumed, never implied.** `rvExp_mulVec` assumes each coordinate
of `ξ` is integrable; `rvCov_mulVec` assumes in addition that each product of two
coordinates is. Both are bundled as `HasMoments`, and no measurability hypothesis
is hidden behind `Integrable`.

* `rvExp_mulVec` : `E[Aξ] = A E[ξ]`.
* `rvExp_affine` : `E[Aξ + b] = A E[ξ] + b`.
* `rvCov_mulVec` : **`Cov(Aξ) = A Cov(ξ) Aᵀ`**, with the summed index in the
  middle, `(A Cov(ξ) Aᵀ) i j = ∑ k ∑ l, A i k Cov(ξ) k l A j l`. No symmetry of
  `Cov(ξ)` is used — the *transpose* is what carries the second index.
* `rvCov_affine` : `Cov(Aξ + b) = A Cov(ξ) Aᵀ` — a constant shifts the mean and
  leaves the covariance alone.

`IsWhiteNoise μ ε σ²` is exactly "`ε` has mean `0` and covariance `σ²I`", i.e. a
first- and a second-moment condition and nothing more. On top of it, `GeoDa.Multiplier`'s
invertibility and the reduced forms of `GeoDa.ReducedForm` give the model moments:

* `sar_moments` : for `y = (1 - ρW)⁻¹ (Xβ + ε)`, `E[y] = (1 - ρW)⁻¹ Xβ` and
  `Cov(y) = σ² A Aᵀ`. The lag puts `A` on *both* sides.
* `sem_moments` : for `u = (1 - λW)⁻¹ ε` and `y = Xβ + u`, `Cov(y) = Cov(u) =
  σ² B Bᵀ`; the regressors contribute nothing.
* `gns_moments` : for `u = Bε` and `y = A(γ + Bε)` with `γ := Xβ + WXθ`,
  `Cov(u) = σ² B Bᵀ` and `Cov(y) = σ² (AB)(AB)ᵀ`.
* `affine_moments`, `linear_moments` : the underlying computation, `E[Aε + c] = c`
  and `Cov(Aε + c) = σ² A Aᵀ`.

**No distributional claim.** `IsWhiteNoise` is a moment condition; no shape is
assumed and in particular **no Gaussianity**. A multivariate normal innovation, and
a likelihood built on it, would be strictly stronger and are not formalized here —
see the [next steps](#next-steps).

### Numerical cross-checks (`validation/`)

`GeoDa` proves the formulas; `validation/` checks that the same formulas, computed a
second time with NumPy, SciPy and PySAL `spreg`, give the same answers. It is a
cross-check, **not a proof**, and it does not replace `./scripts/verify.sh`: the Python
code is not verified and floating-point arithmetic carries no theorem.

The two sides are independent, which is what makes the comparison worth making. Lean
proves `gnsDes_iff_reducedForm`; `spreg.dgp.dgp_gns` computes `(I - λW)⁻¹u`, then
`xb + wxg + u1`, then `(I - ρW)⁻¹` of that — the same theorem written as code; and
`validation/geoda_reference.py` computes it a third way with linear solves. The test
`test_lean_golden_instance_gns_reduced_form` is where they meet: it runs the exact
instance that `GeoDaTest/Smoke.lean` proves outright in `wswap_gns_reducedForm_values`
and checks both Python computations return the Lean-verified `u = [2, 2]` and
`y = [26/3, 34/3]`.

The suite also pins down the conventions that are the usual source of spurious
"disagreement" — `spreg`'s argument order and its `rho`/`lam` meanings, the island
convention shared by `GeoDa.normalize` and `libpysal`'s `transform="r"`, and the fact
that `spreg`'s *default* `imethod="power_exp"` is a truncated power expansion, which
is why every comparison but one asks for `imethod="true_inv"`. The exception measures
that truncation error and shows it shrinking with `|ρ|` — the numerical shadow of
`GeoDa.isUnit_one_sub_smul_of_rowSubstochastic`. Two Lean counterexamples
(`GeoDaTest.wtwo_not_isUnit`, `GeoDaTest.wneg_not_isUnit`) are reproduced numerically
as well.

`spreg`'s *estimators* are deliberately not used anywhere in the suite, and neither is
its moving-average error process, which has no counterpart in `GeoDa`.

## Scope and non-claims

This is a formalization of *model equations*, plus the first two moments of the
resulting random variables. It does **not** establish identifiability, estimator
consistency, asymptotic distribution theory, or numerical correctness, and it
assumes no distributional shape for the innovations. It makes no novelty claim about the mathematics: the
nesting results are textbook (Anselin), the reduced-form statements are matrix
algebra, and the weights predicates are elementary.

In `GeoDa/GNS.lean`, `GeoDa/Weights.lean` and `GeoDa/Design.lean`, `W` is an
arbitrary real matrix: row standardization, symmetry, nonnegativity and any other
regularity of spatial weights are *not* assumed. `GeoDa/SpatialWeights.lean`
makes those regularities available as predicates, but they remain hypotheses of
individual theorems rather than global assumptions, and even there symmetry is
never assumed and a zero diagonal is never assumed. `GeoDa/Multiplier.lean` is
the only place where nonnegativity and row-substochasticity are *used*, and only
to derive invertibility; it still assumes neither symmetry nor a zero diagonal.

`GeoDa/GNS.lean` still takes `Xβ` and `WXθ` as supplied vectors rather than forming
them as matrix products; it is kept exactly as it was so that the theorem
statements pinned in `GeoDaTest/Smoke.lean` do not move. `GeoDa/Design.lean` is
where both terms are formed as actual matrix products.

## Import policy

The project imports the specific Mathlib modules it needs rather than the whole
of Mathlib. Two files reach outside algebra: `GeoDa/Multiplier.lean` imports
`Mathlib.Analysis.Normed.Group.Constructions` for the `ℓ∞` norm on `Fin n → ℝ` and
`Mathlib.Analysis.Normed.Module.Basic` for `norm_smul`, and `GeoDa/RandomVector.lean`
imports `Mathlib.MeasureTheory.Integral.Bochner.Basic` and
`Mathlib.MeasureTheory.Measure.Typeclasses.Probability` for the integral and the
probability-measure class. Everything else stays in algebra. This keeps builds fast and the CI cache small; `import Mathlib` would
pull in all ~8600 Mathlib modules. Note `*ᵥ` is a *scoped* notation, so files
using it need `open scoped Matrix` (and `open Matrix` for the lemma names).

## Verification

Toolchain: Lean `leanprover/lean4:v4.35.0`, Mathlib `v4.35.0`
(`rev 56a005855ea17e0b0958f73ec801ae140b0a1679`); both pinned in `lean-toolchain`
and `lake-manifest.json`.

```
$ ./scripts/verify.sh
==> 1/3  lake build
Build completed successfully (2623 jobs).
==> 2/3  no sorry / admit
     ok: no sorry/admit in any proof
==> 3/3  axiom audit
'GeoDa.gns_iff_sar' depends on axioms: [propext, Classical.choice, Quot.sound]
… (56 theorems, all on the same list)
     ok: all 82 theorems depend only on [propext, Classical.choice, Quot.sound]

VERIFICATION SUCCEEDED
```

Every main theorem depends only on Lean's three standard axioms; none depends on
`sorryAx`, and no additional axiom is introduced.

Two CI workflows run: `Lean` (`.github/workflows/lean.yml`) runs `./scripts/verify.sh`
on GitHub-hosted runners via
`leanprover/lean-action`, which installs the pinned toolchain, fetches the Mathlib
cache and builds. It triggers on `push` to `main`/`master`, on `pull_request` and on
`workflow_dispatch` — note that pushing a feature branch on its own starts nothing.

`lean-action`'s GitHub build cache is deliberately disabled (`use-github-cache:
false`). Its save step archives the whole `.lake` tree — Mathlib's oleans included —
and on an `ubuntu-latest` runner that exhausts the disk. It had never produced a
usable cache entry, and on 2026-10-13 it failed a `main` run with
`zstd: error 70 : Write error : cannot write block : No space left on device`,
skipping the verification step altogether. The Mathlib oleans come from
`lake exe cache get`, which the action still runs, so the build itself is unaffected.

`Validation` (`.github/workflows/validation.yml`) is a separate, lightweight job that
installs the pinned `validation/requirements.txt` and runs the numerical cross-checks
above. It is a second opinion on the formulas, never the verification: a green
`Validation` job says nothing about the theorem statements, and a red one does not
invalidate a proof.

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
the CI configuration were added in the same pass. `GeoDa/Design.lean`, which forms
`Xβ` and `WXθ` as matrix products, was added afterwards in the same way. All of it
was produced with Claude (Claude desktop), **not** with Codex: if the milestone
requires the proofs to be Codex's own work, they should be re-derived
independently and the two versions compared.

## Next steps

1. State the *SAR and SEM* reduced forms under `det ≠ 0` as well. The GNS ones
   already are (`gnsDes_iff_reducedForm_of_det_ne_zero`, via
   `isUnit_iff_det_ne_zero`), and `GeoDa.Multiplier` derives the hypothesis from
   the weights for SAR and SEM; the theorems in `GeoDa.Weights` and
   `GeoDa.Design` that take `IsUnit` directly are unchanged.
2. **A multivariate normal innovation, and a likelihood built on it.** This is
   the stretch goal of the probability layer and is strictly stronger than
   `IsWhiteNoise`: it fixes a distribution, not two moments. Keep it a separate
   claim.
3. Numerical cross-checks against PySAL `spreg`, now that `Xβ` and `WXθ` are
   explicit matrix products, the reduced form covers GNS itself, and the
   invertibility hypothesis is discharged from `|ρ| < 1` and the weights.
