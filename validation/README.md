# Numerical validation harness

This directory cross-checks the formulas that `GeoDa/` **proves** against the
computation that NumPy, SciPy and PySAL `spreg` actually perform.

## What this is not

**Nothing here is verified, and passing these tests is not a substitute for
`./scripts/verify.sh`.**

The Lean development is the verification. `./scripts/verify.sh` builds every module,
greps the sources for `sorry`/`admit`, and audits the axioms of all 82 main theorems.
That is a proof of the identities.

These tests do something different and strictly weaker: they compute the *same*
formulas a second time, with `numpy.linalg.solve` and with `spreg`'s data-generating
processes, and check that the answers agree to a stated tolerance. Passing them is
evidence that

* the formulas were transcribed correctly, and
* the formal objects coincide with what a real implementation computes,

which is exactly what makes a numerical cross-check a cross-check. It is not a proof
of anything, and it cannot be: the Python code is not verified, and floating-point
arithmetic carries no theorem.

## Why a cross-check is meaningful here

The Lean side and the Python side are independent, not two renderings of one idea:

* Lean proves `GeoDa.gnsDes_iff_reducedForm`: the GNS system is *equivalent* to
  `u = B⁻¹ε`, `y = A⁻¹(Xβ + WXθ + B⁻¹ε)`, with `A = I - ρW`, `B = I - λW`.
* `spreg.dgp.dgp_gns` computes `(I - λW)⁻¹u`, then `xb + wxg + u1`, then
  `(I - ρW)⁻¹` of that. That is the same theorem, written out as code.
* `geoda_reference.py` computes it a third way, with linear solves.

`test_lean_golden_instance_gns_reduced_form` is the meeting point: it runs the exact
instance that `GeoDaTest/Smoke.lean` proves outright in `wswap_gns_reducedForm_values`
(`W = Wswap`, `X = [[1],[2]]`, `β = [3]`, `θ = [-1]`, `ε = [1,1]`, `ρ = λ = 1/2`) and
checks that both Python computations return the Lean-verified `u = [2, 2]` and
`y = [26/3, 34/3]`.

## Running the suite

```
python -m venv .venv
.venv/bin/pip install -r validation/requirements.txt
.venv/bin/python -m pytest validation -q
```

CI runs the same thing in a separate job; see `.github/workflows/validation.yml`.

## Layout

```
geoda_reference.py       reference implementations mirroring the Lean definitions
test_model_formulas.py   the cross-checks of the formulas
test_benchmark.py        tests for the benchmark harness
benchmark/               Monte Carlo study of the spreg *estimators* (see its own README)
pytest.ini               silences spreg's own deprecation warnings
requirements.txt         pinned dependencies
```

## Parameterization and conventions

Getting these wrong is the usual source of a spurious "disagreement", so they are
stated explicitly.

* **Weights.** A zero entry of the dense matrix means *no link*. A row that is
  entirely zero is therefore an **island**, with no neighbours — the same convention
  as `GeoDa.Island`, and the same one `libpysal` uses. `to_pysal_W` builds the
  `libpysal` object from the dense matrix and sets `transform = "r"`, and
  `test_lean_golden_instance_normalization` checks that its row standardization
  agrees with `GeoDa.normalize` on both a positive-row matrix and an island one.
  Islands are *not* a division by zero in either implementation.
* **Argument order.** `spreg`'s DGP functions take `(u, xb, [wxg,] w, rho, lam, ...)`
  — the error first, then the deterministic part, then the weights. The coefficient
  `rho` is the **lag** parameter and `lam` the **error** parameter, matching
  `GeoDa`'s `ρ` and `λ`. `wxg` is `WXθ`, i.e. `(W * X) *ᵥ θ`, *not* `W` applied to `y`.
* **Inverse method.** `spreg`'s default is `imethod="power_exp"`, a *truncated power
  expansion* of the spatial multiplier. Every comparison in this suite except one
  passes `imethod="true_inv"` so that the truncated series' error cannot be mistaken
  for a disagreement about the formula. The one exception,
  `test_spreg_default_power_exp_is_a_truncated_neumann_series`, measures that error and
  shows it shrinking with `|ρ|` — which is the numerical shadow of
  `GeoDa.isUnit_one_sub_smul_of_rowSubstochastic`, where `‖W *ᵥ v‖ ≤ ‖v‖` for
  nonnegative row-substochastic `W` (`GeoDa.norm_mulVec_le`) is what makes the series
  converge for `|ρ| < 1`.
* **Variance convention.** `IsWhiteNoise μ ε σ²` is `Cov(ε) = σ²I` with the centered
  covariance of `GeoDa.RandomVector`. The tests here only touch first moments
  (`y`, `u`), so the convention does not arise; see the `GeoDa.RandomVector` section of
  the top-level `README.md`.
* **`model="ma"`.** `dgp_gns(..., model="ma")` uses a moving-average error,
  `u1 = u + λWu`. That is **not** the GNS error process this repository formalizes, so
  it is deliberately not tested rather than silently mapped onto `u = λWu + ε`.
  Likewise `dgp_lagerr` is GNS with `θ = 0`, and is tested only in that reading.

## Tolerances and degenerate cases

* `TOL = 1e-10` for the pure-NumPy comparisons, which are well conditioned by
  construction. The `spreg` comparisons use `1e-8`, since `spreg` goes through a
  sparse-matrix inverse rather than a solve.
* `test_invertibility_fails_at_the_stability_boundary` shows `I - ρW` is singular at
  `ρ = 1` for row-stochastic `W`: `GeoDa.Multiplier`'s `|ρ| < 1` is not slack.
* `test_nonnegativity_and_substochasticity_are_both_needed` reproduces the two Lean
  counterexamples `GeoDaTest.wtwo_not_isUnit` and `GeoDaTest.wneg_not_isUnit`
  numerically: `|ρ| < 1` alone does not suffice for an arbitrary `W`.
* `test_island_weights_are_still_invertible_below_one` covers the degenerate
  island matrix.

## The benchmark, one step further out

`benchmark/` samples from the same data-generating processes and studies the
**estimators** — bias, RMSE, 95% coverage, runtime — rather than the formulas. It is
further still from a proof: the numbers are about `spreg`, not about `GeoDa`, and no
Lean theorem is supported or undermined by any of them. `benchmark/README.md` carries
the model/estimator support matrix and says which combinations `spreg` cannot fit at
all. A CI-scale smoke run executes in the same workflow; the extended grid is opt-in.

## What this harness does not cover

* Nothing about estimators, consistency or asymptotic theory. `spreg`'s *estimators*
  are deliberately not used here; only its data-generating processes.
* No distributional claim. `IsWhiteNoise` in `GeoDa/RandomVector.lean` is a two-moment
  condition and no Gaussianity is assumed or tested.
* The moving-average error process, and any model for which `GeoDa` has no equation.
* Nothing here fits a GNS estimator with `θ ≠ 0` and `λ ≠ 0`: `spreg` has none, and the
  benchmark raises rather than substituting a different estimator. See
  `benchmark/README.md`.
