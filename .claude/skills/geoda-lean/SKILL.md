---
name: geoda-lean
description: Work on the GeoDa-Lean Lean 4 + Mathlib formalization of the GNS spatial econometric models — add or prove a theorem, extend the spatial-weights or multiplier development, declare a new model with the spatial_model DSL, or check that a claim in this repository is actually verified. Use when the task involves GeoDa.lean, GeoDa/, GeoDaTest/, ./scripts/verify.sh, or any claim about SAR/SEM/SDM/GNS being formalized here.
---

# Working on GeoDa-Lean

## Read this first, every time

1. `AGENTS.md` — the task protocol and the fail-closed rules.
2. `CLAUDE.md` — layout, hard rules, and the environment gotchas that have already cost
   hours. It is the canonical working notes; do not re-derive what is in it.

## The verification command

```
./scripts/verify.sh
```

Exits non-zero on the first failure. It runs `lake build`, greps the sources for
`sorry`/`admit`, and checks that every theorem in `GeoDaTest/Axioms.lean` depends only on
`[propext, Classical.choice, Quot.sound]`. Expected tail:

```
     ok: all 92 theorems depend only on [propext, Classical.choice, Quot.sound]
VERIFICATION SUCCEEDED
```

**Never say a result is verified without a passing run of this command, and never say it
for a result you have not run it on.** If the proof will not close, say that instead.
That distinction is the point of the repository.

Note that `EXPECTED_COUNT` in `scripts/verify.sh` is exact: adding a main theorem means
bumping it, in the same commit.

## What lives where

| file | what |
| --- | --- |
| `GeoDa/GNS.lean` | the models, abstractly: `W` is an `ℝ`-linear endomorphism |
| `GeoDa/Weights.lean` | the models with `W` a concrete matrix |
| `GeoDa/Design.lean` | `X`, `β`, `θ`; `Xβ` and `WXθ` as matrix products |
| `GeoDa/SpatialWeights.lean` | the weights predicates, row normalization, islands |
| `GeoDa/Multiplier.lean` | `\|ρ\| < 1 ⇒ IsUnit (1 - ρ • W)` from the weights |
| `GeoDa/ReducedForm.lean` | the full GNS reduced form, both equations |
| `GeoDa/RandomVector.lean` | expectation, covariance, the model moments |
| `GeoDa/DSL.lean` | `spatial_model`: a model's `def` from its equation |
| `GeoDa/Nesting.lean` | SLX, and GNS with both spatial coefficients off |
| `GeoDaTest/Smoke.lean` | `#check` pins and concrete numerical examples |
| `GeoDaTest/Axioms.lean` | the axiom audit; every main theorem appears here |
| `validation/` | numerical cross-checks against NumPy/SciPy/PySAL — **not** verification |
| `docs/DSL-RFC.md`, `docs/agent-tasks.md` | the DSL design; the benchmark record |

## Adding a theorem

1. State it in an existing file if it belongs there, in a new one if it does not. Prefer
   adding to an existing file over duplicating machinery.
2. Prove it. `lake build GeoDa` for the library; `lake env lean /tmp/probe.lean` for a
   scratch file — but note that this does **not** rebuild the files it imports, so build
   first or you will debug a stale version.
3. Reuse before re-proving: `GeoDa.mulVec_eq_iff`, `GeoDa.one_sub_smul_mulVec_eq_iff`,
   `GeoDa.isUnit_one_sub_smul_of_rowSubstochastic`, and the `GeoDa.SpatialWeights`
   predicates are all there to be used.
4. Pin it in `GeoDaTest/Smoke.lean` with `#check @GeoDa.YourTheorem`.
5. Audit it in `GeoDaTest/Axioms.lean` with `#print axioms GeoDa.YourTheorem`.
6. Bump `EXPECTED_COUNT` in `scripts/verify.sh`.
7. Run `./scripts/verify.sh`. Report its tail.

## Adding a model

Use the DSL rather than writing the definition out:

```
spatial_model MyModel {n k : ℕ} (W : WMat n) (X : DMat n k) (y : Vec n) (β : Vec k)
    (θ : Vec k) (ε : Vec n) : y = X *ᵥ β + (W * X) *ᵥ θ + ε
```

It generates an ordinary `def`, checks that every identifier in the equation is declared
and that the declared dimensions are consistent, and nothing else. `docs/DSL-RFC.md`
explains what it does not do and why. If the model is one of the existing ones, prove the
generated def equal to the hand-written one by `rfl` — see `GeoDaTest/DSL.lean`.

## Things that will bite

* **Never widen a hypothesis to make a proof close.** If the proof needs it, the
  statement changes visibly or the task is reported unresolved.
* **Do not cite `validation/` as evidence for a theorem.** It is numerical, and empirical
  checks do not replace formal proofs.
* **`λ` is not an identifier in Lean** — it is the lambda token. The spatial-error
  parameter is `lam` throughout.
* **`Matrix.mulVec_one` is stated under `respectTransparency false`**; use
  `Matrix.mulVec_apply_eq_sum` for row-sum arguments.
* **A docstring cannot precede a custom command** such as `spatial_model`.
* **`open MeasureTheory`** is needed before `[IsProbabilityMeasure μ]`.
* The full list is in `CLAUDE.md`. Add to it when you lose an hour to something new.

## Reporting

Say which of the three happened: **verified** (with the `./scripts/verify.sh` tail),
**refuted** (with the counterexample, proved or exhibited), or **unresolved** (with what
was tried). List every assumption added or modified, and every theorem statement that
moved. If nothing moved, say that too.
