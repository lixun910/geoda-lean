# Research note: the heterogeneous-`ρ` spatial autoregression

Status: pilot. Formalized and machine-checked in `GeoDa/HeteroRho.lean`; checked numerically
in `validation/test_hetero_rho.py`; **no novelty is claimed for any of it.**

This note separates four things that are easy to blur together: what is *known* in the
literature, what is *formalized* here, what is *checked numerically*, and what remains an
*open obligation*. Only the second is machine-verified, and none of it is new mathematics.

---

## 1. The model

Every spatial model in this repository before now has a single autoregressive parameter
`ρ`, shared by all `n` regions. The heterogeneous version gives each region its own:

```
y = diag(ρ) W y + Xβ + ε
```

so that region `i`'s neighbours' outcomes enter with coefficient `ρ i`. Writing
`R := diag(ρ)` and `A := 1 - RW`, the reduced form is `y = A⁻¹ (Xβ + ε)`, and the
expectation and covariance follow from `GeoDa.sar_moments` with `A⁻¹` in place of the scalar
multiplier — nothing new is needed on the probability side.

The two hypotheses are stated explicitly rather than assumed:

* `W` is **nonnegative and row-substochastic** (`GeoDa.Nonneg`, `GeoDa.RowSubstochastic`) —
  the same hypotheses `GeoDa.Multiplier` uses for the scalar case. Islands are allowed;
  symmetry and a zero diagonal are not assumed.
* the parameters are **uniformly bounded**: `|ρ i| ≤ c` for a single `c < 1`. This is
  genuinely stronger than `|ρ i| < 1` for each `i`, and for `Fin n` the two are equivalent —
  but the uniform bound is what the estimate produces, so it is what is assumed. Whether a
  non-uniform hypothesis would suffice is not addressed here.

## 2. Known theory

**The model is not new, and neither is the phenomenon in §4.** What follows is a
literature survey; the references were located by search and **have not been read in
full**, so they should be verified before being cited.

### 2.1 The heterogeneous spatial autoregression

The model with a parameter per unit is established, under two names.

* In spatial econometrics it is the **heterogeneous SAR (HSAR)** of Aquaro, Bailey and
  Pesaran, who write `y_it = ψ_i Σ_j w_ij y_jt + β_i' x_it + ε_it` and, in the compact form
  that matches this note, `(I_N − Ψ₀W) y = B₀x + ε₀` with `Ψ₀ = Diag(ψ₀)`. Their QML
  treatment includes local almost-sure identification conditions, consistency and
  asymptotic normality, and a mean-group estimator for the average spatial effect.
  *(CESifo Working Paper 7542.)*
* In the network literature it is the **heterogeneous peer-effects** model, written
  `Y = ℒWY + …` with `ℒ = diag(λ̃)` and reduced form `Y = [I_N − ℒW]⁻¹(…)`, as in Trinh and
  Montoya-Blandón's finite-mixture SCHSAR, where the `λ` are type-specific and estimated by
  Bayesian MCMC. *(arXiv:2606.24850.)*

The identification question is treated by, among others, Arduini, Patacchini and Rainone
(*The Econometrics of Networks*, 2020), and — for the peer-effects reading of the same
algebra — by Herstad, Houndetoungan and Shin (arXiv:2410.14317), who build on the
friends-of-friends exclusion restrictions of Bramoullé, Djebbari and Fortin (2009).

### 2.2 Islands

That a region with no neighbours contributes nothing to a spatial lag is the "**isolates**"
case of Anselin and Rey, *Modern Spatial Econometrics in Practice*, §3.1.5.1: the isolate's
spatial lag is identically zero, row-standardization of a zero row is undefined, and the
autoregressive parameter's estimate is affected unless the case is handled explicitly.

The same issue appears in software. The `spdep` vignette on no-neighbour observations and
subgraph handling encodes zero rows as a policy choice (`zero.policy`), and `adjust.n`
subtracts isolated units from `N` "to acknowledge the reduction in information". Herstad et
al. handle isolated individuals explicitly, and note that in some parameterizations the
presence of isolated units is what *identifies* other parameters — the zero-row observations
are informative about the absence of interaction. Pereda-Fernández and Zacchia study
identification of network effects with spatially endogenous covariates; Trinh and
Montoya-Blandón exclude isolated firms from their empirical network.

### 2.3 What that means for this note

**The model is known. The reduced form is known. The identification condition of §4 is an
elementary algebraic fact that the spatial-weights literature has discussed for as long as
zero rows have existed.** Nothing in this note is a new method, a new estimator, or a new
identification strategy, and nothing here is offered as one.

## 3. What is formalized

`GeoDa/HeteroRho.lean`, machine-checked, with the axioms audited by `./scripts/verify.sh`:

| statement | name |
| --- | --- |
| `diag(ρ) W *ᵥ v = fun i => ρ i * (W *ᵥ v) i` | `GeoDa.diagMul_mulVec` |
| `‖diag(ρ) W *ᵥ v‖ ≤ c ‖v‖` for a uniform bound `c` | `GeoDa.norm_mulVec_diagMul_le` |
| **existence and uniqueness**: `1 - diag(ρ)W` is a unit | `GeoDa.isUnit_one_sub_diagMul_of_rowSubstochastic` |
| **reduced form**: `y = (1 - diag(ρ)W)⁻¹ (Xβ + ε)` | `GeoDa.heteroSARDes_iff_reducedForm` |
| `ρ ↦ diag(ρ) W` is injective when no row is an island | `GeoDa.diagMul_injective_of_no_island` |
| **identification**: the reduced form determines `ρ` | `GeoDa.heteroSAR_parameter_identified` |
| **non-identification**: an island's `ρ` changes nothing | `GeoDa.heteroSARDes_island_invariant`, `GeoDa.heteroSAR_reducedForm_island_invariant` |

The novelty claim is deliberately minimal and is about *verification*, not about
mathematics: these statements are checked by a kernel, and they are the first place in this
repository with a theorem about recovery from a full reduced-form map. Whether
that is worth anything to anyone else is for others to judge.

## 4. Algebraic parameter recovery (not statistical identifiability)

**Claim.** `ρ i` is determined by the reduced form if and only if row `i` of `W` is not an
island.

*If row `i` is an island*, then `(diag(ρ) W) i j = ρ i · W i j = 0` for every `j`, whatever
`ρ i` is. Two parameter vectors differing only in `ρ i` therefore give the same multiplier,
hence the same structural equation, hence the same solutions and the same reduced form. No
data generated by this model can separate them. That is
`GeoDa.heteroSARDes_island_invariant`.

*If no row is an island*, then from `diag(ρ) W = diag(ρ') W` one gets
`(ρ i - ρ' i) · W i j = 0` for all `i, j`, and for each `i` some `j` with `W i j ≠ 0` forces
`ρ i = ρ' i`; so `ρ ↦ diag(ρ) W` is injective. Combined with the invertibility of the
multiplier — which makes the reduced form determine `1 - diag(ρ)W` — this gives
`GeoDa.heteroSAR_parameter_identified`.

Both directions are proved. Note what the claim is and is not: it is about the *reduced
form as a function of `(Xβ, ε)`*, an algebraic object. It is not a statement about
estimation from data, which §6 leaves open.

## 5. Numerical evidence

`validation/test_hetero_rho.py`, run in CI. It is a **check on an independent
implementation, not evidence for the theorems**, and not an estimator evaluation.

* **The island's parameter is exactly invisible.** With `W` equal to `GeoDaTest.Wisland`,
  `ρ = (1/4, 1/2)` and `ρ = (3/4, 1/2)` give **bit-identical** simulated data — not close,
  identical, at the level of `np.array_equal`. This is the strongest form the check can
  take, and it is the point: no estimator separates what the model cannot distinguish.
* **Away from islands the parameter is visible.** The same experiment on
  `GeoDaTest.Wswap`, which has no zero row, gives different data.
* **A prototype estimator, and why it is not one.** Reconstructing `ρ` coordinatewise from
  the structural equation, `ρ i = (y_i - z_i) / (W y)_i` with `z = Xβ + ε`, recovers `ρ` to
  round-off when no row is an island and returns `nan` at an island, where the numerator and
  denominator are both zero. It is *not a feasible estimator*: it needs `ε`. It is recorded
  because it makes the identifiability boundary visible, and because recording a prototype
  that is deliberately not feasible is more honest than dressing it up.
* **The uniform bound is not slack.** At `c = 1` with a row-stochastic `W`, the multiplier
  `1 - diag(1)W` is singular; inside the interior it is not.

## 6. Open obligations

Recorded rather than hidden. **None of these is addressed by the Lean development**, and
none of them should be assumed to hold.

1. **A feasible estimator.** The prototype of §5 needs `ε`. No feasible estimator for `ρ`
   at fixed `n` is proposed or validated here. That `ρ` is determined by the reduced form
   says nothing about whether it can be estimated, at what rate, or with what finite-sample
   behaviour.
2. **Asymptotics.** No consistency, rate, or asymptotic distribution is claimed for any
   estimator of this model. Aquaro–Bailey–Pesaran do provide such results for the panel
   case; nothing of the kind is formalized here.
3. **The uniform bound.** Whether the uniform hypothesis `∃ c < 1, ∀ i, |ρ i| ≤ c` can be
   relaxed — to `|ρ i| < 1` individually, or to a spectral condition on `diag(ρ)W` — is
   open here. For finite `n` the two are equivalent; the question is what a more general
   `W` admits.
4. **Inference under a constraint.** In practice `ρ` is not free per observation; it is
   usually a function of covariates, `ρ i = g(z_i'γ)`. The constrained model, its
   identification, and the estimator it suggests are all outside this note.
5. **Endogenous or misspecified `W`.** The model takes `W` as given and known. Nothing here
   survives `W` being estimated or endogenous, which is the setting of Pereda-Fernández and
   Zacchia.
6. **Substantive identification beyond islands.** The claim of §4 says `ρ` is determined by
   the reduced form when there are no islands. It does **not** say the design matrix `X`
   has enough variation in any particular application, and it does not address the
   rank conditions the literature imposes on `(I, W, W²)`.

## 7. Reproducibility

```
./scripts/verify.sh                                   # builds and audits the Lean side
python -m pytest validation -q                        # the numerical checks
```

`GeoDa/HeteroRho.lean` can be read on its own; the identifiability pair is in its last
section, and both directions carry docstrings stating exactly what they do and do not say.
`GeoDaTest/HeteroRho.lean` pins the signatures and instantiates both directions on
`Wisland` and `Wswap`. Every theorem named in §3 is audited in `GeoDaTest/Axioms.lean`, and
`EXPECTED_COUNT` in `scripts/verify.sh` counts them.

## 8. What is not claimed

* **No novelty.** The model, the reduced form and the identification condition are all
  known; see §2.
* **No estimator.** No claim that `ρ` can be estimated, consistently or otherwise.
* **No empirical application.** A simulated model, not a dataset.
* **Nothing about `W` being correct.** `W` is an input, assumed known and fixed.
* **No claim about the rest of the repository.** The heterogeneous model is a
  demonstration that the existing machinery — `GeoDa.SpatialWeights` for the island
  predicate, `GeoDa.Multiplier` for the contraction, `GeoDa.ReducedForm` for the reduced
  form, `GeoDa.RandomVector` for the moments — composes. If it had not, that would have
  been the finding.
