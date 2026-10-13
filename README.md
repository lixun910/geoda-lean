# GeoDa Lean: formalizing the GNS nesting of spatial econometric models

Lean 4 + Mathlib formalization of the equation-level nesting of the General
Nesting Spatial (GNS) model into SAR, SEM and SDM, together with the full GNS
reduced form and the SAR/SEM/SDM reduced forms under an invertibility
assumption, and the spatial weights predicates (nonnegativity, row
standardization, islands) those models are stated over.

**Status:** baseline `eb53ae6` records successful verification of 115 audited
results. The Paper 1 revision adds two results (117 audit entries total), and full
verification of them has been **observed**: locally, `./scripts/verify.sh` exits 0,
and CI agrees (`Lean` run `38481135562`), both ending `ok: all 117 theorems depend
only on [propext, Classical.choice, Quot.sound]` then `VERIFICATION SUCCEEDED`. See
[the validation record](paper/verification.md). Do not treat the baseline transcript
as evidence for these additions, and do not carry either run past a commit that
changes a proof or a statement.

## Contents

```
GeoDa.lean                root module
GeoDa/GNS.lean            abstract version: W is an arbitrary ℝ-linear endomorphism
GeoDa/Weights.lean        concrete version: W is a real n×n matrix; reduced forms
GeoDa/Design.lean         design matrix X; Xβ and WXθ formed by matrix product
GeoDa/ReducedForm.lean    the full GNS reduced form, eliminating u and y together
GeoDa/Multiplier.lean     invertibility of 1 - ρW from the weights themselves
GeoDa/RandomVector.lean   probability layer: expectation, covariance, model moments
GeoDa/DSL.lean            a `spatial_model` command: a model from its equation alone
GeoDa/Nesting.lean        SLX, and GNS with both spatial coefficients switched off
GeoDa/HeteroRho.lean      the heterogeneous-ρ model: reduced form and algebraic parameter recovery
GeoDa/Sdem.lean           the spatial Durbin error model: nestings and reduced form
GeoDa/SpatialWeights.lean weights predicates, row normalization, islands
GeoDaTest/DSL.lean        the DSL's tests: rfl-equivalence and pinned rejections
GeoDaTest/AgentTasks.lean the agent-loop benchmark, including the refuted conjectures
GeoDaTest/HeteroRho.lean  the heterogeneous-ρ tests: map injectivity and island invariance
GeoDaTest/Sdem.lean       the SDEM tests: nestings, reduced form, and the DSL equivalence
GeoDaTest/Smoke.lean      compile-time tests (signature pins, explicit examples)
GeoDaTest/Axioms.lean     axiom audit, driven by scripts/verify.sh
scripts/verify.sh         the verification suite
validation/               numerical cross-checks against NumPy, SciPy and PySAL spreg
validation/benchmark/     Monte Carlo bias/RMSE/coverage study of spreg estimators
docs/DSL-RFC.md           the design of the `spatial_model` DSL
docs/agent-tasks.md       the agent-loop benchmark: three tasks and what they returned
docs/research-note-heterogeneous-rho.md  the research pilot: prior art, findings, open obligations
docs/research-note-sdem.md   the P4.2 benchmark: prior art, fidelity check, workflow metrics
AGENTS.md                 working notes for agents; points at CLAUDE.md
.claude/skills/geoda-lean/ a reusable Skill: the conventions and the protocol
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
  of all supplied vectors `(xb, ε)` exactly when both inverse matrices are the
  identity. This is equality of deterministic reduced-form maps, not equality of
  observable probability distributions. It does not establish statistical
  identifiability for a fixed design or innovation distribution. The previous
  item establishes a map equality *after transforming the regressors*.

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

This module assumes invertibility. `GeoDa.Multiplier` derives it from nonnegative
row-substochastic weights and an absolute parameter bound below one.

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
truncation error on selected inputs. The Lean theorem establishes invertibility,
not a bound on implementation error or a proof of the stopping criterion. Two Lean counterexamples
(`GeoDaTest.wtwo_not_isUnit`, `GeoDaTest.wneg_not_isUnit`) are reproduced numerically
as well.

`spreg`'s *estimators* are deliberately not used anywhere in the suite, and neither is
its moving-average error process, which has no counterpart in `GeoDa`.

### Monte Carlo benchmark (`validation/benchmark/`)

`validation/` checks the *formulas* numerically. `validation/benchmark/` goes one step
further out and studies the **estimators**: it samples from the exact data-generating
processes `GeoDa/` formalizes, fits `spreg` estimators, and reports bias, RMSE, 95%
coverage, runtime and failure counts as machine-readable output under
`results/smoke/`.

This is the furthest thing in the repository from a proof. `GeoDa/` proves statements
about *model equations* and says nothing about estimators, consistency or asymptotic
distributions; the numbers there are about `spreg`, not about `GeoDa`, and every one is
a finite-sample estimate. They are not evidence for any Lean theorem.

These finite-sample experiments can flag estimator behavior worth investigating.
The invertibility theorem does not imply a bound on estimation bias or coverage;
trends in the smoke grid are descriptive and are not an explanation of estimator failure.

Two things are stated rather than papered over. `spreg` has **no estimator for GNS with
`θ ≠ 0` *and* `λ ≠ 0`** — the model `GeoDa.GNSDes` writes down — so `SUPPORT["gns"]` is
empty and the harness *raises* rather than fitting something close and labelling it GNS.
And `GM_Combo` reports no standard error for `lambda`, so its coverage is reported as
absent with the reason rather than computed from a misaligned error.

The CI-scale smoke run executes in CI; the `--extended` grid is opt-in and its outputs
are not committed.

### A DSL for model specifications (`GeoDa.DSL`)

Adding a model used to mean writing the equation out again with its binder list. The
`spatial_model` command writes the `def` for you from the equation alone:

```
spatial_model MySLX {n k : ℕ} (W : WMat n) (X : DMat n k) (y : Vec n) (β : Vec k)
    (θ : Vec k) (ε : Vec n) : y = X *ᵥ β + (W * X) *ᵥ θ + ε
```

generates an ordinary `def`, which `#print` shows, which `#check` pins, and about which
anything can be proved as usual.

It is Lean-native, and that is the design decision, argued in
[`docs/DSL-RFC.md`](docs/DSL-RFC.md): the equation is elaborated by Lean's own
elaborator, so there is no compiler to trust and no trust boundary to argue about. The
alternative — an external specification language plus a source generator — would make
the generator a trusted component, and would have to be *checked* anyway, at which
point it has bought a second language for nothing.

Two failures that Lean would otherwise let through silently are rejected instead.
Because the generated definition is elaborated under `autoImplicit false`, a coefficient
that appears in the equation but not in the binder list is an error rather than a
silently introduced implicit parameter — which would have produced a *different* model
than the one written. And the declared slot types are inspected for dimensional
consistency, which catches a slot whose dimension the equation never pins down and
Lean's own type checker therefore cannot see.

What it does **not** do is generate theorems or check the mathematics. It cannot: whether
the equation is the model you meant is not a formal property. Nor does it check that `W`
is row-standardized, nonnegative or connected — those are the predicates of
`GeoDa.SpatialWeights`, to be required by the theorems that need them rather than by the
syntax that names a model.

The equivalence to the hand-written specifications is mechanical, not argued: the
generated `def`s for SAR, SDM, SEM and GNS are proved equal to `SARDes`, `SDMDes`,
`SEMDes` and `GNSDes` by **`rfl`** — the same function up to definitional equality. A
fifth model, SLX, has no counterpart in the repository and costs one equation.

### The agent loop (`AGENTS.md`, `docs/agent-tasks.md`)

The repository is set up to be driven by an automated agent, and to hold one to the same
standard a human is held to. `AGENTS.md` states the task protocol and the fail-closed
rules; `.claude/skills/geoda-lean/SKILL.md` is the reusable Skill carrying the
conventions; `docs/agent-tasks.md` records three benchmark tasks run end to end.

The third of those is the one that matters. It states a conjecture that is **false** —
that every *nonnegative* weights matrix gives an invertible spatial multiplier for
`|ρ| < 1`, a natural over-generalization of `isUnit_one_sub_smul_of_rowSubstochastic`. The
loop's job was not to find a proof. It was to report, correctly, that there is none — and
the refutation is not a remark in a log file but two theorems,
`GeoDaTest.nonneg_alone_is_not_enough` and
`GeoDaTest.rowSubstochastic_alone_is_not_enough`, proved from counterexamples that were
already in the test suite.

What the loop demonstrates is a claim about the *process*: that a hypothesis can be driven
to a kernel-checked theorem through a fixed protocol, and that a false claim is reported
as false rather than replaced by a nearby true one. It does not demonstrate that the
theorems are the right ones, that the models are the models the literature means, or that
any estimator is consistent. No statement in this repository is claimed to be novel.

### Research pilot: heterogeneous autoregressive parameters (`GeoDa.HeteroRho`)

`GeoDa/HeteroRho.lean` formalizes one model that is *not* in the rest of the repository:
the **heterogeneous-`ρ`** spatial autoregression, `y = diag(ρ) W y + Xβ + ε`, where every
region has its own autoregressive parameter. It is a **known** model — the heterogeneous
SAR of Aquaro, Bailey and Pesaran in spatial econometrics, the heterogeneous peer-effects
model of the network literature — and no novelty is claimed for it or for anything proved
about it. `docs/research-note-heterogeneous-rho.md` gives the prior art and is explicit that
the references were located by search and not read in full.

What is machine-checked: **existence and uniqueness** of the solution, for nonnegative
row-substochastic `W` and parameters uniformly bounded by a single `c < 1` — the estimate
that `GeoDa.Multiplier` proves for a scalar `ρ`, with the scalar bound replaced by a bound
on every coordinate; the **reduced form** `y = (1 - diag(ρ)W)⁻¹ (Xβ + ε)`, its expectation
and covariance then following from `sar_moments` unchanged; and **algebraic parameter
recovery from the full reduced-form map**. `ρ i` is determined by the reduced form exactly when row `i` of `W` is not an
island: an island's parameter multiplies a zero row and is invisible to the model, so two
values of it generate identical data; and when no row is an island, `ρ ↦ diag(ρ) W` is
injective, so the reduced form recovers `ρ` uniquely. That is the formal counterpart of the
"isolates" discussion in Anselin and Rey, §3.1.5.1.

`validation/test_hetero_rho.py` checks the same statements numerically — the island case
gives **bit-identical** simulated data for two different parameter vectors, which is the
strongest form the check can take.

The map-injectivity result is neither statistical identifiability nor an estimator result.
Equality of observable distributions at a fixed design is a different premise from
equality of the reduced-form maps for every supplied `(xb, ε)`. A prototype that
recovers `ρ` from the structural equation is recorded, and it is labelled as **not
feasible**, because it needs `ε`. Whether `ρ` can be estimated, at what rate, and under what
design, is left as an open obligation, along with five others, in §6 of the research note.
Nothing here makes an empirical claim, and no estimator is validated.

### The P4.2 benchmark: SDEM (`GeoDa.Sdem`)

`GeoDa/Sdem.lean` formalizes the **spatial Durbin error model** — `y = Xβ + WXθ + u`,
`u = λWu + ε` — as a *reproduction* of published results rather than a new development. It is
the benchmark model of the P4.2 pilot, chosen because there is a reference to be wrong against:
it is in LeSage and Pace's *Introduction to Spatial Econometrics* (2009), LeSage (2014) singles
it out as one of two specifications applied work should consider, and PySAL implements its DGP.

The formalization is mostly *assembly*, which is what a benchmark on an established model
should be. SDEM is GNS with `ρ = 0` (`gnsDes_iff_sdemDes`), so it reuses the existing machinery;
`sdemDes_iff_slx_and_error` shows it is SLX with a spatial error and is `Iff.rfl`, an identity
rather than an argument; `sdemDes_iff_slxDes_of_lam_zero` and `sdemDes_iff_semDes_of_theta_zero`
are the two nestings LeSage (2014) states — SDEM subsumes SLX and SEM — and are the closest
thing here to a semantic-fidelity check, since the published claim is exactly a relation
between named models. The reduced form `y = Xβ + WXθ + (1 - λW)⁻¹ε` comes with the invertibility
hypothesis *derived* from the weights, and the moments from `sem_moments` unchanged.

The numerical cross-check is against **PySAL's** DGP, not ours: `spreg.dgp.dgp_slxerror`
computes exactly the reduced form, so agreement is not circular. Two failure cases are
recorded: `spreg`'s default `imethod="power_exp"` *refuses* rather than degrades near `|λ| = 1`,
because its Euclidean increment-norm guard can reject a convergent series. This
is distinct from mathematical invertibility. Islands preserve existence; the
parameter-invariance result concerns observation-specific `ρ`, not scalar SDEM `λ`.

`docs/research-note-sdem.md` carries the prior art, the workflow metrics, and — with more
prominence than the results — what the exercise does **not** show. Chiefly: the original run only searched for papers and was **not blind**. The
Paper 1 revision subsequently checked LeSage (2014), pp. 16 and 19, against the
full source (see `paper/source-map.md`); this does not retroactively make the run blind — the required literature search
returned the reduced form and both nestings, and the repository already contained the same
proof shape for SEM and SAR. It is a demonstration that a published model can be reconstructed
and cross-checked through the existing library; it is not evidence that the workflow scales to
unfamiliar mathematics.

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

Historical baseline transcript (not rerun for the Paper 1 revision):

```
$ ./scripts/verify.sh
==> 1/3  lake build
Build completed successfully (2631 jobs).
==> 2/3  no sorry / admit
     ok: no sorry/admit in any proof
==> 3/3  axiom audit
'GeoDa.gns_iff_sar' depends on axioms: [propext, Classical.choice, Quot.sound]
… (remaining baseline audit entries)
     ok: all 115 theorems depend only on [propext, Classical.choice, Quot.sound]

VERIFICATION SUCCEEDED
```

The Paper 1 revision was rerun — locally, and in CI on a different machine — and both
produce the same output with `all 117 theorems` in place of `all 115`:

```
$ ./scripts/verify.sh     # macOS 26.6.2, Apple M2 Max, Lean 4.35.0 from elan
==> 1/3  lake build
Build completed successfully (2632 jobs).
==> 2/3  no sorry / admit
     ok: no sorry/admit in any proof
==> 3/3  axiom audit
'GeoDa.isUnit_one_sub_smul_of_colSubstochastic' depends on axioms: [propext, Classical.choice, Quot.sound]
'GeoDa.gnsDes_moments_of_rowSubstochastic' depends on axioms: [propext, Classical.choice, Quot.sound]
     ok: all 117 theorems depend only on [propext, Classical.choice, Quot.sound]

VERIFICATION SUCCEEDED
```

The historical baseline audit reports only Lean's three standard axioms; none depends on
`sorryAx`, and no additional axiom is introduced.

Two CI workflows run: `Lean` (`.github/workflows/lean.yml`) runs `./scripts/verify.sh`
on GitHub-hosted runners via
`leanprover/lean-action`, which installs the pinned toolchain, fetches the Mathlib
cache and builds. It triggers on `push` to `main`/`master`, on `pull_request` and on
`workflow_dispatch` — note that pushing a feature branch on its own starts nothing.

The Paper 1 revision has been verified this way: `Lean` run `38481135562` on commit
`f0ee036` (`paper1-semantic-review`, triggered by draft pull request #22) completed
green in 1 m 58 s on 2026-10-13, its audit reporting
`ok: all 117 theorems depend only on [propext, Classical.choice, Quot.sound]` and
then `VERIFICATION SUCCEEDED`. The same job had failed on the revision's first
commit `22ea450`, so the pass belongs to `f0ee036` and to no earlier commit. The
`Validation` run `38481135556` from the same push is green as well, and the two
runs repeat green on later documentation-only commits (head `37ce61d`, run
`38481610834`). What breaks the chain is a commit that changes a proof or a
statement, not a prose edit.

The same revision was verified locally as well, so the CI runs confirm a run rather
than standing in for one: on macOS 26.6.2 (Apple M2 Max, arm64) with Lean 4.35.0 from
elan, `lake update` followed by `lake exe cache get` and `./scripts/verify.sh` took
1 m 51 s in total and the suite exited 0.

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
independently and the two versions compared. The later Paper 1 revision was
prepared with Codex, including two added declarations; its validation status is
recorded separately in `paper/verification.md`.

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
3. Cross-checking against PySAL `spreg` **is** in place: `validation/` compares the
   formulas and `validation/benchmark/` studies the estimators, with the usual caveat
   that neither is verification. What remains is a GNS **estimator** — `spreg` has none
   for `θ ≠ 0` with `λ ≠ 0`, so that model can be simulated but not fitted.

## Paper 1 working manuscript

See [paper/manuscript.md](paper/manuscript.md), the [source map](paper/source-map.md),
and [revision validation record](paper/verification.md). The revision adds
`isUnit_one_sub_smul_of_colSubstochastic` and
`gnsDes_moments_of_rowSubstochastic` (`GeoDa/ModelMoments.lean`).
