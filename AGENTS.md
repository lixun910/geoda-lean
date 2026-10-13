# Working notes for agents

This file is for automated agents (Codex, Claude, or anything else) working on this
repository. **`CLAUDE.md` is the canonical working notes and this file deliberately does
not repeat it** — an earlier revision was a copy, and it drifted out of date within two
pull requests. Read `CLAUDE.md` first: layout, the verification command, the hard rules,
the theorem-statement discipline, and the environment gotchas that have already cost
hours.

What follows is only what is *specific to working as an agent here*: the task protocol,
the failure modes that matter, and the loop this repository is set up to be driven
through. A worked record of three benchmark tasks is in `docs/agent-tasks.md`.

## The one command that decides everything

```
./scripts/verify.sh
```

It builds every target, greps the sources for `sorry`/`admit`, and audits the axiom
footprint of every main theorem. Exits non-zero on the first failure.

**Never report a result as verified without a passing run of this command, and never
describe a result you have not run it on.** If a proof will not close, say so. This
repository exists to make that distinction sharp; an agent that blurs it is worse than
useless here.

## Task protocol

1. **Natural language → formal statement.** Write down what is to be proved, in Lean, in
   a file that already builds. Get the *statement* right before attempting the proof,
   and state every hypothesis explicitly. Do not widen a hypothesis to make a proof go
   through — that is the same error as a wrong proof, and harder to notice.
2. **Look for the existing lemma first.** The machinery is probably already here:
   `GeoDa.mulVec_eq_iff`, `GeoDa.one_sub_smul_mulVec_eq_iff`, and the whole of
   `GeoDa.SpatialWeights` exist to be reused. Re-proving an estimate is how the two
   versions drift apart.
3. **Attempt the proof.** `lake build` early and often. `lake env lean <file>` is useful
   for a scratch file, but it does **not** rebuild what `<file>` imports — see the
   gotcha in `CLAUDE.md`.
4. **Read the compiler, do not guess.** Lean's errors name the metavariables. Fix the
   actual failure rather than adding `simp` until the goal disappears.
5. **Record the outcome honestly: verified, refuted, or unresolved.** All three are
   results. "Unresolved" is not a failure of the loop; claiming "verified" for an
   unresolved claim is.
6. **Pin and audit.** New main theorems go in `GeoDaTest/Smoke.lean` (a `#check` pin) and
   `GeoDaTest/Axioms.lean` (an `#print axioms`), and `EXPECTED_COUNT` in
   `scripts/verify.sh` is bumped to match. Never change an existing theorem's statement
   or an existing pin to make something compile: an existing statement changing *is* the
   failure being guarded against.

## Fail closed

An agent working here must fail closed on all of the following. Each is enforced by
`./scripts/verify.sh` unless noted.

* **No `sorry`, no `admit`, no new `axiom`.** Enforced.
* **No statement changes without review.** Diffing `GeoDaTest/Smoke.lean` is the check;
  a changed `#check` line in a PR means a theorem statement moved. Not machine-enforced —
  a reviewer's job.
* **No silently strengthened (or weakened) hypotheses.** If the proof needs a hypothesis
  the statement does not have, the *statement* is what changes, visibly, or the task is
  reported unresolved.
* **No claim of verification from a partial run.** `lake build` succeeding is not the
  verification; the axiom audit is part of it, and a red CI run is a red result.
* **No "it works in Python".** `validation/` and `validation/benchmark/` are numerical
  cross-checks and an empirical study of `spreg` estimators. They verify nothing, and are
  explicitly not evidence for any theorem. Do not cite them as such.
* **No novel mathematics claimed.** Nothing in this repository claims to be new, and its
  scope notes say so. Keep it that way.

## Sandboxed workflow

* Work on a feature branch, never on `main`. The app's worktree setup already does this;
  keep the branch name tied to the issue.
* One issue per branch and per pull request.
* A pull request description must list every assumption **added or modified**, every
  theorem statement that moved, and the exact `./scripts/verify.sh` tail as evidence.
  If nothing was added or moved, say that too — it is a fact a reviewer wants.
* Do not merge a pull request whose CI has not been observed to pass.

## Limits of the loop

The loop demonstrates that a claim can be driven from a natural-language hypothesis to a
kernel-checked theorem, and that it fails loudly when it cannot. It does **not**
demonstrate that the theorems are the right ones, that the model is the model the
literature means, or that any estimator is consistent. `docs/agent-tasks.md` records both
a task that succeeded and a conjecture that the loop correctly *refused* to verify.

`GeoDa/DSL.lean` exists to remove the boilerplate between steps 1 and 3: a model's
definition can be generated from its equation alone by `spatial_model`. Its design, and
the trust question it does not have, are in `docs/DSL-RFC.md`.
