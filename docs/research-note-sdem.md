# Research note: SDEM as the P4.2 benchmark model

Status: complete for Phases A–C; Phase D is reported below, including the parts that went
badly.

The model is `GeoDa/Sdem.lean`; the tests are `GeoDaTest/Sdem.lean`; the numerical
cross-check is `validation/test_sdem.py`. **This is a reproduction of published results, not
a discovery.** Nothing here is offered as new mathematics, and §6 explains in what sense even
the "reproduction" was not blind.

---

## 1. The benchmark question

> Can an AI coding agent use this Lean library to reconstruct, formally verify and
> numerically validate the spatial Durbin error model — with its nesting relations, its
> reduced form and its moments — against the published statements?

Precisely what is being reproduced:

| claim | published in | formalized as |
| --- | --- | --- |
| `y = Xβ + WXθ + u`, `u = λWu + ε` | LeSage & Pace (2009) | `GeoDa.SDEMDes` |
| reduced form `y = Xβ + WXθ + (I − λW)⁻¹ε` | LeSage (2014) | `GeoDa.sdemDes_iff_reducedForm` |
| SDEM subsumes SLX when `λ = 0` | LeSage (2014) | `GeoDa.sdemDes_iff_slxDes_of_lam_zero` |
| SDEM subsumes SEM when `θ = 0` | LeSage (2014) | `GeoDa.sdemDes_iff_semDes_of_theta_zero` |
| `u = (I − λW)⁻¹ε = (I + λW + λ²W² + ⋯)ε` | LeSage (2014) | the same reduced-form theorem |

## 2. Phase A — prior art, and what I did not do

**SDEM** is the *spatial Durbin error model*: spatially lagged regressors together with a
spatially autocorrelated disturbance, and no lag of `y`. It is in LeSage and Pace,
*Introduction to Spatial Econometrics* (CRC Press, 2009).

LeSage (2014), "What Regional Scientists Need to Know About Spatial Econometrics", singles it
out — with the SDM — as one of only two specifications applied work should consider, writes it
as `y = Xβ₁ + WXβ₂ + u` with `u = λWu + ε`, derives the own- and cross-partial derivatives
`∂yᵢ/∂Xᵢₖ = β₁` and `∂yᵢ/∂Xⱼₖ = Wβ₂`, and states the two nestings formalized here: SDEM
subsumes SLX when `λ = 0` and SEM when `β₂ = 0`.

Halleck Vega and Elhorst (2015), "The SLX Model", *Journal of Regional Science* 55(3),
339–363, place SDEM in the small group — SLX, SDEM, SDM, GNS — whose spillover effects are
*flexible* across regressors, as against SAR and SAC, which impose a constant ratio between
spillover and direct effects, and SEM, whose spillovers are zero by construction. Their
comparison table and Figure 1 are the standard reference for where SDEM sits. Rüttenauer
(2019/2022), *Sociological Methods & Research* 51(2), 728–759, writes the specification out as
equation (6) and reports Monte Carlo evidence on direct and indirect impacts. Burridge (1981)
is the common-factor test that discriminates the SDM from error-dependence specifications;
Bramoullé, Djebbari and Fortin (2009) is the source for the rank condition on `(I, W, W²)`
that the SLX literature cites alongside it.

### The caveat that matters

**I have searched for these sources, not read them.** The summaries above come from search
results and secondary descriptions, and the equations attributed to LeSage (2014) are
reproduced as the search reported them. The fidelity check in §3 is therefore a comparison
against *my reading of summaries of the sources*, and a human who has the book open should
check it. This is the weakest link in the whole pilot and it is stated here rather than
buried: **the issue asked for the papers to be read, and they were not.**

What survives that caveat is the structural evidence: SDEM is unambiguously expressible in
the existing GNS with `ρ = 0`, and the two nestings are unambiguous from the equations
themselves — `λ = 0` removes the autocorrelation and leaves SLX's equation term for term,
and `θ = 0` removes the lagged regressors and leaves SEM's. Even without the papers, there is
only one thing these nestings can be.

## 3. Phase B — the formalization, and the fidelity check

`GeoDa/Sdem.lean`, eight theorems, all audited:

* `gnsDes_iff_sdemDes` — GNS with `ρ = 0` is SDEM. This is what makes SDEM a *benchmark*
  rather than a new development: it needs no new algebra.
* `sdemDes_iff_slx_and_error` — SDEM is SLX with a spatial error. **This one is `Iff.rfl`**:
  the `y`-equation of SDEM is literally `SLXDes` with the disturbance left named `u`. LeSage's
  "subsumes" is, at equation level, an identity.
* `sdemDes_iff_slxDes_of_lam_zero`, `sdemDes_iff_semDes_of_theta_zero` — the two published
  nestings. These are the closest thing here to a semantic-fidelity check: the published
  claim is a *relation between named models*, and the theorem is that relation.
* `sdemDes_iff_reducedForm`, `sdemDes_iff_reducedForm_of_rowSubstochastic` — the reduced form,
  the second with the invertibility hypothesis derived from the weights rather than assumed
  (`GeoDa.Multiplier`) so that the statement carries `Nonneg`, `RowSubstochastic` and
  `|λ| < 1` instead of an opaque `IsUnit`.
* `sdem_moments` — the mean and covariance, from `GeoDa.sem_moments` with `Xβ + WXθ` in place
  of `Xβ`. Not re-derived.

Phase B also asks for a typed specification via the DSL. `GeoDaTest/sdemViaDsl_eq_SDEMDes`
declares SDEM with `spatial_model` and proves the generated definition equal to the
hand-written `SDEMDes` by **`rfl`** — the same function up to definitional equality.

### Assumptions

**None were added beyond the model's own, and none was strengthened.** The hypotheses that
appear are `Nonneg W`, `RowSubstochastic W`, `|λ| < 1` and `IsUnit (1 - λW)` on the reduced
form side, and `HasMoments` / `IsWhiteNoise` on the probability side — exactly the ones the
corresponding existing theorems already carry. The model statement itself, `SDEMDes`, assumes
nothing about `W`, as every model definition in this repository does.

## 4. Phase C — numerical cross-check, and its tolerances

`validation/test_sdem.py`, 13 tests, run in CI. The point of the design is that the reference
is **not ours**: `spreg.dgp.dgp_slxerror` implements the SDEM DGP in PySAL, doing
`u₁ = (I − λW)⁻¹u`, `y = xb + wxg + u₁`, which is `sdemDes_iff_reducedForm` in somebody else's
code.

| check | result |
| --- | --- |
| `dgp_slxerror` vs the reference reduced form, `imethod="true_inv"`, seeds 0–5 | agree to `1e-8` |
| islands (a zero row) | agree; existence survives, as `rowSubstochastic` predicts |
| `λ = 0` gives SLX | exact; `u = ε` to `1e-10` |
| `θ = 0` gives SEM | agrees with `dgp_sperror` to `1e-8` and with `sem_reduced` to `1e-10` |
| the two nestings are independent | at `λ = 0.4` both `λ ↦ 0` and `θ ↦ 0` change `y` |

Tolerances are `1e-10` for the pure-NumPy comparisons and `1e-8` for the `spreg` ones, which
go through a sparse inverse rather than a solve.

### The failure case

`spreg`'s default `imethod="power_exp"` is a truncated power expansion, and near `|λ| = 1`
it does **not** merely lose accuracy — it refuses:

```
Exception: power expansion will not converge, check model specification and that weight are less than 1
```

At `λ = 0.2` it agrees to better than `1e-9`; at `λ = 0.99` it raises. That is the right
behaviour and still a failure worth recording, and it is the numerical shadow of the Lean
hypothesis: `GeoDa.isUnit_one_sub_smul_of_rowSubstochastic` gets invertibility from
`‖W *ᵥ v‖ ≤ ‖v‖` with `|λ| < 1`, which is exactly the condition under which the series
converges. Every comparison above asks for `"true_inv"` so that this cannot be mistaken for a
disagreement about the model. (`spreg`'s `model="ma"` moving-average error, which is not this
model, remains untested, as in `validation/README.md`.)

## 5. Phase D — the workflow metrics, reported honestly

| metric | measurement |
| --- | --- |
| proof success | 9 / 9 audited theorems. Nothing was attempted and abandoned; nothing was weakened to close. |
| agent effort | 4 build–fix cycles: 4 errors on the first compile of the library, then 2, then 1; 3 errors on the first compile of the tests. Wall-clock for the whole task was under an hour, most of it the two `lake build` cycles. |
| human effort | 3 interventions, all *scope*, none *mathematical*: the user replaced the issue text with the reproduction framing, directed that PR #20 be merged first, and named SDEM. The user did not supply a proof, correct a statement, or fix a lemma. |
| assumption quality | no assumption added or strengthened (§3). |
| mathematical fidelity | §2's table: the two nestings and the reduced form match the published statements **as reported by search, not as read in the sources**. |
| numerical fidelity | agrees with PySAL's independent implementation to `1e-8`. |
| reproducibility | below. |

The intervention count is the number that should be treated with most suspicion, and not
because it is low: it counts *one* agent on *one* task with a human watching throughout, and
`docs/agent-tasks.md` records how much of the difficulty was already removed by the existing
repository. It is a single paired observation, not a rate.

## 6. What this does *not* demonstrate — benchmark integrity

The issue requires that completed proofs not be handed to the agent, and that the context be
recorded. Here is the honest accounting, and it is not flattering:

* **No Lean proof of SDEM was supplied.** That rule was kept.
* **But the answer was available anyway.** The literature search that Phase A required
  returned the reduced form `y = Xβ + WXθ + (I − λW)⁻¹ε` and both nestings, in the search
  results themselves. A "blind" reproduction it was not.
* **And the repository had already removed the difficulty.** `GeoDa/Design.lean` contains
  `gnsDes_iff_semDes` and `gnsDes_iff_sarDes`, whose proofs are the same three lines; the
  SDEM nesting proofs are those lines with a different middle term. `GeoDa/ReducedForm.lean`
  and `GeoDa/Multiplier.lean` supply the reduced-form pattern and the invertibility
  hypothesis. The task was therefore *assembly*, not *discovery*, which is what a benchmark
  on an established model should be — but it means the run says very little about how the
  workflow would fare on something the repository does not already almost contain.

So: this is a demonstration that a *published* model can be reconstructed and cross-checked
against an independent implementation through the existing library, with the proof obligations
stated. It is **not** evidence that the workflow scales to unfamiliar mathematics, and it is
not evidence about productivity in general. A genuinely blind version of this benchmark would
need a task whose answer is not already in the agent's search results and not already
three-quarters in the repository — which is a description of the P5 track, not of this one.

## 7. What is not claimed

* **No novelty.** SDEM, its reduced form and both nestings are published; §2.
* **No estimator.** Nothing here estimates `λ`, `β` or `θ`, and nothing is said about
  consistency, rates, or direct/indirect impact estimation. The partial-derivative
  interpretation of LeSage (2014) is *not* formalized: this repository has no calculus of
  spatial impacts.
* **No empirical application.**
* **No verified fidelity to the sources.** The papers were not read (§2).
* **No claim about the rest of the repository.** As with the heterogeneous-`ρ` pilot, what
  the exercise does show is that the existing machinery composes.

## 8. Reproducibility

```
./scripts/verify.sh                     # builds and audits the Lean side: 115 theorems
python -m pytest validation -q          # the numerical cross-checks: 95 tests
```

`GeoDa/Sdem.lean` can be read on its own; the two published nestings are one section of it.
`GeoDaTest/Sdem.lean` pins the signatures, instantiates the nestings at `n = 2`, and carries
the DSL equivalence. Every theorem named in §3 is audited in `GeoDaTest/Axioms.lean`, and
`EXPECTED_COUNT` in `scripts/verify.sh` counts them — currently 115, up from 106.

Dependencies are pinned in `validation/requirements.txt` and were resolved and run green on
CPython 3.14.2 (NumPy 2.5.4, SciPy 1.18.1, libpysal 4.15.0, spreg 1.9.1, pytest 9.1.1). CI
runs both workflows on every pull request.
