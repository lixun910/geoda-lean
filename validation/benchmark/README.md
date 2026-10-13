# Monte Carlo benchmark for `spreg` estimators

Samples data from the exact data-generating processes that `GeoDa/` formalizes, fits
PySAL `spreg` estimators, and reports how often and how far the estimates miss the
parameters used to generate the data.

## Empirical checks do not replace formal proofs

This directory is **not** part of the verification, and nothing in it supports or
undermines any Lean theorem.

`GeoDa/` proves statements about *model equations* — identities, equivalences,
invertibility — and says nothing about estimators, consistency or asymptotic
distributions. The numbers here are about `spreg`, not about `GeoDa`. Every one of them
is an estimate from a finite sample and carries no proof obligation and no proof. The
verification is `./scripts/verify.sh`; see the top-level `README.md`.

What the benchmark *is* good for is the other direction: it checks that the equations
this repository writes down are the equations an implementation fits, and it shows
where an estimator's behaviour stops being trustworthy — near the stability bound, and
with islands.

## The model/estimator support matrix

| model | equation | `spreg` estimators here |
| --- | --- | --- |
| `sar` | `y = ρWy + Xβ + ε` | `ML_Lag` (ML), `GM_Lag` (GM/2SLS) |
| `sem` | `y = Xβ + u`, `u = λWu + ε` | `ML_Error` (ML), `GM_Error_Hom` (GM, homoskedastic) |
| `sdm` | `y = ρWy + Xβ + WXθ + ε` | `ML_Lag` on `[X, WX̃]` |
| `sarar` | `y = ρWy + Xβ + u`, `u = λWu + ε` | `GM_Combo` (GM) |
| `gns` | `y = ρWy + Xβ + WXθ + u`, `u = λWu + ε` | **none** |

**`spreg` has no estimator for GNS with `θ ≠ 0` *and* `λ ≠ 0`.** That is the model
`GeoDa.GNSDes` writes down with both terms live, and it is why `SUPPORT["gns"]` is the
empty tuple. The harness raises if you ask for it; it never fits something close and
labels it GNS. `sarar` is the `θ = 0` case of GNS and is labelled as such.

`GM_Lag` and `GM_Error_Hom` are the alternative (non-ML) estimators for SAR and SEM.
They are in the matrix but only in the **extended** configuration: the smoke run fits
one estimator per model, so that CI stays cheap.

## Assumptions each estimator makes

Stated because they are the difference between "this estimator is inconsistent" and
"this estimator was asked for something it does not assume".

* `ML_Lag`, `ML_Error`, `ML_Lag_Durbin` — maximum likelihood. They assume the
  innovations are i.i.d. normal. They are the efficient choice when that holds and are
  not robust to it failing.
* `GM_Lag`, `GM_Error_Hom`, `GM_Combo` — method of moments. No distributional
  assumption, robust to non-normality, less efficient than ML. `GM_Error_Hom` and
  `GM_Combo` nonetheless assume **homoskedasticity**; there are `_Het` variants in
  `spreg` for when that is too strong, and they are not used here.
* All of them take the weights matrix as given and assume it is non-singular after the
  spatial filter — that is, that `I - ρW` and `I - λW` are invertible. Under `GeoDa`'s
  hypotheses on the weights, `GeoDa.Multiplier` proves this for `|ρ|, |λ| < 1`; the
  benchmark stays inside that regime.

Getting `betas`' layout wrong would silently produce numbers that are *not* the
parameters you think they are, so `benchmark.py` declares each estimator's layout in
`ESTIMATORS` and checks it. One estimator is not consistent with the others: **`GM_Combo`
reports no standard error for `lambda`**, so its `std_err` has one entry fewer than
`betas`. That is declared in `no_se=("lam",)` and asserted in `fit`, so the errors
cannot shift by one. Coverage is then reported as `null` for `lambda`, with the reason,
rather than as a number computed from a misaligned error.

## Configurations

```
python validation/benchmark/benchmark.py --list       # the support matrix
python validation/benchmark/benchmark.py --smoke      # CI scale -> results/smoke/
python validation/benchmark/benchmark.py --extended   # opt-in   -> results/extended/
```

* **smoke** — 8 cells, 7×7 lattice (`n = 49`), 50 replications each, `ρ = 0.5` and
  `ρ = 0.8`, one island cell. About two seconds. Runs in CI.
* **extended** — 4 models × up to 2 estimators × lattice sides `{5, 10, 20}` ×
  `islands ∈ {False, True}` × `ρ ∈ {0.2, 0.5, 0.8, 0.95}` × 250 replications. Minutes,
  and its outputs are **not** committed. Opt in explicitly; it is not a CI job.

## What is measured

Per cell and per parameter, over the replications that produced a finite estimate:

* **bias** — `mean(estimate) − true value`;
* **RMSE** — `sqrt(mean((estimate − true value)²))`;
* **coverage** — the share of replications whose `estimate ± 1.96 · std_err` contains
  the true value. It should be near `0.95` for a well-calibrated estimator that is
  reporting honest standard errors; with 50 replications the Monte Carlo error on this
  is a few percent, so read it as a smoke alarm, not a measurement.
* **failures** — replications that raised, or that returned a non-finite estimate.
  These are **counted and reported, never dropped silently and never replaced by
  another estimator's output**.
* **seconds** — wall-clock time for the cell. The only field that is not reproducible
  run to run.

Replications are seeded: cell `c`, replication `r` uses
`numpy.random.default_rng(c.seed_base + r)`. A run is reproducible from the config.

## Reading the results

`results/<tag>/summary.csv` is one row per (cell, parameter). `results/<tag>/<label>.json`
carries the same rows plus the full cell configuration and the estimator's own
description, so a row can be interpreted without reconstructing the config.

Two things the smoke numbers already show, both of which are about `spreg` and not
about `GeoDa`:

* bias in `ρ` and in the intercept grows as `ρ` moves from `0.5` to `0.8` toward the
  stability bound, which is what `GeoDa.Multiplier`'s `|ρ| < 1` hypothesis is guarding;
* the island cell still fits, because a zero row is substochastic and `I - ρW` is still
  invertible — the same reason `GeoDa.isUnit_one_sub_smul_of_rowSubstochastic` covers
  it.

Neither observation is a proof of anything, and neither is evidence for a Lean
theorem. They are a sanity check that the model this repository formalizes is the model
being fitted.
