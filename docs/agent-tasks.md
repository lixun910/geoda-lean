# The agent loop: three benchmark tasks, and what they returned

This is the record for the P4.1 issue: a reproducible agent loop that proposes Lean
definitions and proofs, runs Lean, and reports the result honestly. The protocol and the
fail-closed rules are in `AGENTS.md`; the reusable instructions are in
`.claude/skills/geoda-lean/SKILL.md` and `CLAUDE.md`.

Three tasks were run end to end. One was a **new nested model relation**, one an
**invertibility theorem**, and one a **false conjecture**. The third is the point of the
exercise: the loop's job is not to produce proofs, it is to produce *correct reports*, and
the case that distinguishes a working loop from a plausible one is the case where the
answer is "no".

## The protocol, as run

1. Write the statement in Lean, in a file that builds, with every hypothesis explicit.
2. Look for the existing machinery before proving anything.
3. Prove. `lake build` after every few lines.
4. Read the compiler's error and fix the actual failure.
5. Report **verified**, **refuted** or **unresolved** — and nothing in between.
6. Pin (`GeoDaTest/Smoke.lean`), audit (`GeoDaTest/Axioms.lean`), bump `EXPECTED_COUNT`.

Nothing about this protocol is specific to an LLM; what it tests is whether an agent can
be held to it.

---

## Task A — a new nested model relation

**Hypothesis.** SLX (*spatial lag of X*), `y = Xβ + WXθ + ε`, is a fifth model alongside
SAR, SEM, SDM and GNS. It should be exactly GNS with both `ρ` and `λ` switched off.

**Result: verified.**

**What was added.** `GeoDa/Nesting.lean`:

* `GeoDa.SLXDes` — the model equation, `y = X *ᵥ β + (W * X) *ᵥ θ + ε`;
* `GeoDa.gnsDes_iff_slxDes` — GNS with `ρ = 0`, `λ = 0` is `SLXDes` together with `u = ε`.

**What the loop had to get right, and got right after reading the compiler.**

* The `u = ε` clause. GNS keeps a latent disturbance that SLX absorbs, so the
  equivalence is with `SLXDes ∧ u = ε`, not with `SLXDes`. Writing the statement without
  it would have been false. `gnsDes_iff_sarDes` and `gnsDes_iff_sdmDes` in
  `GeoDa/Design.lean` carry the same clause, and the existing proof shape transferred
  directly — step 2 of the protocol earned its place.
* `λ` cannot be written as an identifier, so the spatial-error coefficient is `lam`
  throughout, as everywhere else in the repository.
* `abel` after `simp only [zero_smul]`, not `simp`: after `simp [GNSDes, SLXDes]` the goal
  lands in a shape `simp` will not close. This is a known gotcha in `CLAUDE.md` and did
  not have to be rediscovered.

**Repair iterations: 1** — the first attempt omitted the `u = ε` clause and was rejected by
the type checker when the reverse direction was attempted.

---

## Task B — an invertibility theorem

**Hypothesis.** `GeoDa.Multiplier` proves `1 - ρW` invertible for nonnegative
row-substochastic `W` and `|ρ| < 1`. The **column**-substochastic case — column sums at
most one, as in a column-standardized weights matrix — should give the same for the
*transposed* multiplier `1 - ρ • Wᵀ`.

**Result: verified.**

**What was added.** A section at the end of `GeoDa/Multiplier.lean`:

* `GeoDa.colSum`, `GeoDa.ColSubstochastic` — the dual predicates;
* `GeoDa.rowSum_transpose` — the row sums of `Wᵀ` are the column sums of `W` (`rfl`);
* `GeoDa.isUnit_one_sub_smul_transpose_of_colSubstochastic` — the theorem.

**What the loop had to get right.**

* **Which norm is controlled.** Nonnegative column-substochasticity makes `Wᵀ` an
  `ℓ∞` contraction, but need not make `W` one. Both `1 - ρ • Wᵀ` and `1 - ρ • W`
  are nevertheless invertible for `|ρ| < 1`, because transposition preserves
  invertibility. The earlier account incorrectly called the latter conclusion false.
  The direct corollary is `isUnit_one_sub_smul_of_colSubstochastic`.
* **Reuse, not re-proof.** `Wᵀ` is nonnegative and row-substochastic exactly when `W` is
  nonnegative and column-substochastic, both by `rfl`, so
  `isUnit_one_sub_smul_of_rowSubstochastic` applies to `Wᵀ` unchanged and the whole
  theorem is one line. Repeating the `ℓ∞` estimate for columns would have been a second
  copy of the same argument, free to drift from the first.

**Repair iterations: 2** — the first attempt applied the theorem to `Wislandᵀ` instead of
`Wisland` in the test, producing `1 - ρ • Wislandᵀᵀ`; the second corrected the
column-substochasticity witness. Both were caught by the type checker, not by inspection.

---

## Task C — a false conjecture

**Hypothesis.** Every *nonnegative* weights matrix gives an invertible spatial multiplier
for `|ρ| < 1`:

```
∀ W ρ, Nonneg W → |ρ| < 1 → IsUnit (1 - ρ • W)
```

It is a natural over-generalization of `isUnit_one_sub_smul_of_rowSubstochastic`, and the
question is whether the loop reports it correctly.

**Result: refuted.** The loop did **not** produce a proof, and no statement was weakened
to make one possible.

**Why it is false.** Nonnegativity imposes no bound on the row sums. `2 • 1` is
nonnegative, its rows sum to `2`, and at `ρ = 1/2` the multiplier is `1 - (1/2)·2·1 = 0`,
which is not a unit. The missing hypothesis is `RowSubstochastic`.

**What was added.** `GeoDaTest/AgentTasks.lean`, turning the refutation into a checked
fact rather than a remark in a log:

* `GeoDaTest.nonneg_alone_is_not_enough` — the negation of the universal statement,
  proved from the counterexample `GeoDaTest.wtwo_not_isUnit`;
* `GeoDaTest.rowSubstochastic_alone_is_not_enough` — and the dual over-generalization,
  dropping nonnegativity instead, refuted by `GeoDaTest.wneg_not_isUnit`.

**Repair iterations: 0 for the claim** — the loop recognized the failure mode and stopped.
That is the outcome the task exists to test.

**The failure that did not happen, and would have.** A loop optimizing for "a theorem
appeared" would have found that `Nonneg W → |ρ| < 1 → IsUnit (1 - ρ • W)` is *provable*
for `n = 0` and for `W = 0`; that it holds whenever `RowSubstochastic` happens to hold;
and that it becomes true if `|ρ| < 1` is strengthened to `ρ = 0`. Any of those is a
theorem, none is the conjecture, and each would have been a false report. The
counterexample is already in `GeoDaTest/Smoke.lean` — the loop's job was to *look*.

---

## Recorded verification

No theorem statement in the repository was changed by these three tasks: every addition
is a new declaration, and `GeoDaTest/Smoke.lean`'s existing `#check` lines are untouched.
The new theorems were pinned there and audited in `GeoDaTest/Axioms.lean`, taking
`EXPECTED_COUNT` from 87 to 92.

```
$ ./scripts/verify.sh
'GeoDa.isUnit_one_sub_smul_transpose_of_colSubstochastic' depends on axioms: [propext, Classical.choice, Quot.sound]
'GeoDaTest.nonneg_alone_is_not_enough' depends on axioms: [propext, Classical.choice, Quot.sound]
'GeoDaTest.rowSubstochastic_alone_is_not_enough' depends on axioms: [propext, Classical.choice, Quot.sound]
     ok: all 92 theorems depend only on [propext, Classical.choice, Quot.sound]

VERIFICATION SUCCEEDED
```

## What this does and does not demonstrate

It demonstrates that a claim can be driven from a hypothesis to a kernel-checked theorem
through a fixed protocol, and that the loop reports a false claim as false rather than
finding a nearby true one. That is a claim about the *process*, and it is checkable: the
theorems are in the repository, the refutation is a theorem, and `./scripts/verify.sh` is
the arbiter of all of it.

It does **not** demonstrate that the theorems are the right ones, that the models are the
models the spatial econometrics literature means, or that any estimator is consistent.
Nothing in this repository claims novelty, and `validation/` and
`validation/benchmark/` — the numerical cross-checks and the Monte Carlo study — remain
empirical work that verifies nothing.
