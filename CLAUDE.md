# Working notes for this repository

Lean 4 + Mathlib formalization of the equation-level nesting of the General
Nesting Spatial (GNS) model into SAR, SEM and SDM, with the SAR/SEM reduced
forms under an invertibility assumption.

**Status: compiler-verified.** `./scripts/verify.sh` exits 0 and audits 106 theorems.

## Layout

```
GeoDa.lean             root module (imports all nine libraries)
GeoDa/GNS.lean         abstract: W is an ℝ-linear endomorphism of Fin n → ℝ
GeoDa/Weights.lean     concrete: W is Matrix (Fin n) (Fin n) ℝ, via Matrix.mulVec
GeoDa/Design.lean      design matrix X; Xβ = X *ᵥ β, WXθ = (W * X) *ᵥ θ
GeoDa/ReducedForm.lean full GNS reduced form: u = B⁻¹ε, y = A⁻¹(Xβ + WXθ + B⁻¹ε)
GeoDa/SpatialWeights.lean  weights predicates (Nonneg, RowStochastic, Island, …)
                       and row normalization; no global assumptions added
GeoDa/Multiplier.lean  |ρ| < 1 ⇒ IsUnit (1 - ρ • W) from Nonneg + RowSubstochastic
GeoDa/RandomVector.lean  probability layer: rvExp, rvCov, IsWhiteNoise, model moments
GeoDa/DSL.lean         `spatial_model`: generate a model's `def` from its equation
GeoDa/Nesting.lean     SLX, and GNS with both spatial coefficients off
GeoDa/HeteroRho.lean   the heterogeneous-ρ model: reduced form and identifiability
GeoDaTest/DSL.lean     DSL tests: rfl-equivalence to the hand-written specs, rejections
GeoDaTest/AgentTasks.lean  the agent-loop benchmark's refuted conjectures
GeoDaTest/HeteroRho.lean    heterogeneous-ρ tests: both directions of identifiability
AGENTS.md              the agent protocol; points at this file rather than copying it
docs/agent-tasks.md    the agent-loop benchmark record
docs/research-note-heterogeneous-rho.md  the research pilot
.claude/skills/geoda-lean/  reusable Skill: conventions + the task protocol
GeoDaTest/Smoke.lean   compile-time tests: signature pins + explicit n = 1, 2 examples
GeoDaTest/Axioms.lean  axiom audit, consumed by scripts/verify.sh
scripts/verify.sh      build + no-sorry + axiom audit
validation/            numerical cross-checks vs NumPy/SciPy/PySAL; NOT verification
validation/benchmark/  Monte Carlo bias/RMSE/coverage study of spreg estimators
docs/original-GNS.lean the pre-existing draft, kept verbatim (see "Provenance")
README.md              the user-facing write-up; keep it in step with the code
```

## How to verify — always run this before claiming anything works

```
./scripts/verify.sh
```

It runs `lake build`, greps the sources for `sorry`/`admit`, and checks that all
106 main theorems in `GeoDaTest/Axioms.lean` depend only on
`[propext, Classical.choice, Quot.sound]`. Expected tail:

```
     ok: all 106 theorems depend only on [propext, Classical.choice, Quot.sound]
VERIFICATION SUCCEEDED
```

Toolchain: Lean `leanprover/lean4:v4.35.0`, Mathlib `v4.35.0`
(`rev 56a005855ea17e0b0958f73ec801ae140b0a1679`), pinned in `lean-toolchain` and
`lake-manifest.json`. Do not bump these without re-running the suite.

### First build on a fresh machine

If `lean`/`lake` are absent, install elan (it honours `lean-toolchain`, so it
fetches v4.35.0 automatically):

```
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y
exec "$HOME/.elan/bin/lake" --version
```

Then let lake materialise Mathlib and pull the prebuilt oleans before building —
compiling Mathlib from source takes hours, the cache takes minutes:

```
lake update          # materialises .lake/packages from lake-manifest.json
lake exe cache get   # downloads the prebuilt Mathlib oleans (~5-7 GB)
./scripts/verify.sh
```

Budget ~10 GB of free disk for `.lake` (the toolchain is another ~3 GB under
`~/.elan`). If space is short, `lake exe cache get <module name>` fetches only
that module and its transitive imports — see the gotchas below.

The second CI workflow, `Validation` (`.github/workflows/validation.yml`), installs
`validation/requirements.txt`, runs `python -m pytest validation`, and then runs the
CI-scale Monte Carlo smoke run
`python validation/benchmark/benchmark.py --smoke`. It is a cross-check of the formulas
against NumPy/SciPy/PySAL plus an empirical study of `spreg` **estimators**, **not** a
verification: it says nothing about theorem statements, and a red `Validation` job does
not invalidate a proof. Do not describe it as verifying anything. To run it locally:

```
python -m venv .venv && .venv/bin/pip install -r validation/requirements.txt
.venv/bin/python -m pytest validation -q
.venv/bin/python validation/benchmark/benchmark.py --smoke
```

The benchmark's `results/smoke/` is committed (deterministic except for the wall-clock
`seconds` field); the `--extended` grid is opt-in and gitignored. `spreg` has no
estimator for GNS with `θ ≠ 0` and `λ ≠ 0`, and `validation/benchmark/benchmark.py`'s
`SUPPORT` table says so and raises rather than substituting a different estimator —
keep it that way.

`AGENTS.md` is for automated agents and **deliberately does not repeat this file** — an
earlier revision was a copy of it and drifted out of date within two pull requests. Keep
it a pointer plus the agent-specific protocol; do not let it become a second copy.

## Hard rules

* **No `sorry` and no `admit`**, ever, and no new `axiom`. `scripts/verify.sh`
  enforces both. If a proof will not close, say so rather than papering over it.
* **Never describe a proof as verified without a passing `lake build`.** The
  original draft of `GeoDa/GNS.lean` was labelled a proof but had never been
  compiled and did not parse.
* **Theorem statements are load-bearing.** `GeoDaTest/Smoke.lean` pins every
  signature with `#check` on purpose: changing a statement should be a
  deliberate edit, and the `#check` block updated with it. If you add a theorem
  that belongs to the "main results", add it to both `Smoke.lean` and
  `Axioms.lean` and bump `EXPECTED_COUNT` in `scripts/verify.sh`.
* **Targeted imports, not `import Mathlib`.** The project imports the specific
  Mathlib modules it needs (see the header of `GeoDa/GNS.lean`). `import Mathlib`
  pulls ~8600 modules and makes the build and CI cache enormous.

## Environment gotchas that have already cost hours

* **First build needs the Mathlib cache (5–7 GB).** If the disk is tight, fetch
  only the closure of what you import — `lake exe cache get <module name>` gets
  that module *and everything it imports transitively* — instead of the whole
  cache. Measure the closure first by parsing `import` lines out of the Mathlib
  sources.
* **Do not delete `.git` inside `.lake/packages/*`.** It saves only ~60 MB and
  lake then decides the dependency is not materialized, re-clones it, and fails
  on the existing working tree. Freeing the toolchain's static libs
  (`lib/lean/lib{Lean,Std,Init,Lake}.a`) is safe instead. Deleting
  `.lake/build/ir` is *not* safe — lake treats missing outputs as stale and
  rebuilds.
* **`λ` can never be an identifier in Lean** — it is the lambda token. The draft
  bound the disturbance coefficient as `λ` and therefore could not be parsed;
  it is `lam` throughout now.
* **`*ᵥ` is scoped notation.** Files using it need `open scoped Matrix`, and the
  lemma names (`sub_mulVec`, `one_mulVec`, `mulVec_injective`, `mulVec_zero`, …)
  need `open Matrix`.
* **Mixing a `module` file with a non-`module` file is a hard error**
  ("cannot import non-`module` X from `module`"). This project is consistently
  *non*-module: plain `import`. Expect a benign
  "designed for use with the module system" warning per Mathlib import.
* **`simp` is not reliable here.** It sometimes refuses to close a goal that
  prints as `X = X`, and after `simp [GNS, SAR]` the nesting goals land in the
  shape `(P ∧ Q) ↔ (R ∧ Q)`, which it will not finish. The existing proofs are
  written to be independent of `simp`'s normal form: `calc` plus `abel` (after
  `simp only [zero_smul]`) for vector equations.
* **For `IsUnit.unit`, `rw [← h.unit_spec]` fails** with "motive is not type
  correct" (dependent projection). Use `simpa only [h.unit_spec] using
  Units.inv_mul h.unit` and friends, which normalises the *type* instead.
* **`Matrix.mulVec_mulVec` reads `M *ᵥ N *ᵥ v = (M * N) *ᵥ v`** — the forward
  direction is the one that *combines* two applications. Using `←` there is a
  familiar mistake. Its **explicit argument order is `(v, M, N)`, vector first**:
  `mulVec_mulVec θ W X : W *ᵥ X *ᵥ θ = (W * X) *ᵥ θ`. Writing `mulVec_mulVec W X θ`
  silently unifies `W` with the *vector* slot and fails with a type mismatch whose
  displayed type looks like your goal with the arguments rotated — read the
  metavariable positions, not the shape.
* **`Mathlib/LinearAlgebra/Matrix/Basic.lean` does not exist in v4.35** (split
  into `Defs.lean`, `Module.lean`, …). `Mathlib.Data.Real.Basic` is deprecated in
  favour of `Mathlib.Basic.Real.Basic`.
* **Do not `rw [h]` a *self-referential* hypothesis into a goal that mentions both
  sides.** For `h : v = c • (W *ᵥ v) + w`, `intro h; rw [h]; abel` substitutes `v`
  *everywhere*, including on the right, and leaves a nested mess that `abel` cannot
  close. Use `calc` instead — `calc v = c • (W *ᵥ v) + w := h; _ = … := by abel`.
  Rewriting a hypothesis *at* another hypothesis (`rw [hu] at hy`) is fine; it is
  the goal-level rewrite that bites.
* **`Matrix.mulVec_one` is stated under
  `set_option backward.isDefEq.respectTransparency false`.** So `(W *ᵥ 1) i` is
  *not* definitionally `W i ⬝ᵥ 1` in an ordinary `exact`/`simpa`/`rw`, and
  `Matrix.mulVec_one` itself will not unfold `(W *ᵥ 1) i` for you. Use
  **`Matrix.mulVec_apply_eq_sum : (M *ᵥ v) i = ∑ j, M i j * v j`**, which is
  `rfl`-proved — that is the right entry point for any row-sum argument.
* **`dotProduct` and `dotProduct_one` are *root-level* names**, not
  `Matrix.dotProduct` / `Matrix.dotProduct_one`: `Mathlib/Data/Matrix/Mul.lean`
  defines them in a `section` *outside* `namespace Matrix` (that file does
  `open Matrix` rather than nesting). The `⬝ᵥ` notation is root-level too. There
  is also no `Matrix.rowSum`, so `GeoDa.rowSum` is free.
* **`lake env lean <file>` does not rebuild the files `<file>` imports.** It uses the
  `.olean`s already on disk, so after editing `GeoDa/*.lean` you must `lake build GeoDa`
  before `lake env lean /tmp/probe.lean`, or you will debug the *previous* version of
  your code — which looks exactly like your edit having had no effect, or worse, like a
  bug you have already fixed.
* **A docstring cannot precede a custom command.** `/-- … -/ spatial_model Foo … ` fails
  with "unexpected token 'spatial_model'; expected 'lemma'": Lean's parser attaches a
  docstring to a *declaration*, and a `CommandElab` is not one. Use a `--` comment, or
  have the command put the docstring on the declaration it generates (which
  `spatial_model` does).
* **`IsProbabilityMeasure` is not a root-level name; `open MeasureTheory` first.**
  `Measure` alone resolves at root, so `{μ : Measure Ω}` elaborates, but
  `[IsProbabilityMeasure μ]` then fails with the baffling
  "invalid binder annotation, type is not a class instance ?m.4". Add
  `open MeasureTheory` in the section that needs it.
* **`integral_congr_ae (Eventually.of_forall fun ω => ...)` hands you a beta-redex**
  `(fun ω => ...) ω = (fun ω => ...) ω`, which `rw` will not match against the
  integrand. Start the sub-proof with `show` in beta-reduced form.
* **A scalar literal in a goal defaults to `ℕ`.** `2 • M` in a *statement* is
  `(2 : ℕ) • M` unless you write `(2 : ℝ) • M`, and then `exact`ing a proof that
  produced `(2 : ℝ) • M` fails on the scalar type. Write the cast out.
* **`Matrix.mulVec_add` needs `add_comm` after it** whenever you are aiming at the
  shape `A *ᵥ ε ω + c` that `GeoDa.rvExp_affine` and `GeoDa.rvCov_affine` expect.
* **The `ℓ∞` norm on `Fin n → ℝ` and `norm_smul` are the only `Analysis` imports
  the project needs**, and their module paths are not where you would guess:
  `norm_le_pi_norm` and `pi_norm_le_iff_of_nonempty` live in
  `Mathlib.Analysis.Normed.Group.Constructions` — there is **no**
  `Mathlib.Analysis.Normed.Group.Pi` — and `norm_smul` needs
  `Mathlib.Analysis.Normed.Module.Basic`. `Mathlib.Analysis.Matrix.Normed`
  (`Matrix.linfty_opNorm_mulVec`, and a scoped `NormedRing` instance under
  `open scoped Matrix.Norms.Operator`) also works but is heavier; the vector route
  in `GeoDa/Multiplier.lean` is deliberately elementary.
* **`haveI` on a proposition trips `linter.style.haveILetI`.** To use an
  `IsEmpty`/`Nonempty` hypothesis as an instance, either restructure so you do not
  need one (e.g. build the zero vector with `funext fun i => (h.false i).elim`), or
  accept the warning.
* **A file that imports `GeoDa.ReducedForm` also gains a root-level `normalize`,**
  so a bare `normalize` in `GeoDaTest/Smoke.lean` becomes ambiguous with
  `GeoDa.normalize` once both branches are present. Write `GeoDa.normalize`
  explicitly in tests.
* Passing a hypothesis like `hu : u = … u …` to `simp` loops (recursion depth).

## Provenance — keep this honest

Every proof here was produced by Claude (Claude desktop), **not** by Codex. The
project's stated first milestone is for *Codex* to complete the GNS →
SAR/SEM/SDM formalization independently, so this repository currently serves as a
reference/answer key rather than as evidence for that milestone. `README.md`
says so and `docs/original-GNS.lean` preserves the unverified draft verbatim.
Do not quietly present this work as Codex's, and do not delete that note.

## Mathematical scope — do not overclaim

* These are statements about *model equations*. Nothing here establishes
  identifiability, estimator consistency, asymptotic theory or numerical
  correctness, and nothing here is claimed to be novel.
* `W` is an arbitrary real matrix in `GNS.lean`/`Weights.lean`/`Design.lean`:
  row standardization, symmetry and non-negativity are **not** assumed.
  `SpatialWeights.lean` names those regularities as predicates (`Nonneg`,
  `RowStochastic`, `RowSubstochastic`, `Island`, `ZeroDiag`) so they can be
  *hypotheses*, but they are still not global assumptions, and even there
  symmetry is never assumed. Row standardization does not imply a zero diagonal
  and a zero diagonal does not imply row standardization; both directions are
  proved, so do not silently assume either. Islands are handled by a totalized
  inverse (`(0 : ℝ)⁻¹ = 0`), not by a side condition on `normalize`.
* **SAR and SEM are not observationally equivalent in general.**
  `reducedForm_eq_iff_inverse_eq_one` shows the reduced forms agree for all
  `(Xβ, ε)` exactly when the inverse matrix is the identity (i.e. `ρW = λW = 0`).
  The defensible equivalence statement, and the one formalized, is
  `sem_reducedForm_eq_sar_reducedForm_of_filtered`: a SEM equals a SAR whose
  regressors have been spatially filtered to `(1 - λW)Xβ`. When writing this up,
  use that formulation.

## Next task

The previous "next task" — forming `Xβ` and `WXθ` from a design matrix instead of
taking them as supplied vectors — is **done**: see `GeoDa/Design.lean`. It
introduces `X : Matrix (Fin n) (Fin k) ℝ` with `β θ : Fin k → ℝ`, defines
`GNSDes`/`SARDes`/`SEMDes`/`SDMDes` with `xb := X *ᵥ β` and `wxθ := (W * X) *ᵥ θ`,
and restates the nesting, linear-system, reduced-form and filtered-equivalence
results there. `GeoDa/GNS.lean` and `GeoDa/Weights.lean` are untouched, so the
audit count only grew (12 → 25).

What is left, roughly in order of value:

1. **A feasible estimator for the heterogeneous-ρ model.** `GeoDa/HeteroRho.lean` proves
   that `ρ` is determined by the reduced form away from islands, but a *prototype* that
   recovers it needs `ε`, which no implementation observes. Estimability, rates and
   asymptotics are open; `docs/research-note-heterogeneous-rho.md` §6 lists five further
   obligations of the same kind. Do not describe the identifiability result as an estimator
   result.
2. **A multivariate normal innovation, and a likelihood built on it.** The probability
   layer in `GeoDa/RandomVector.lean` stops at two moments (`IsWhiteNoise`); fixing a
   distribution is strictly stronger and should stay a separate claim. This is the
   stretch goal of the P1.1 issue, not started.
3. **Templated statements.** `GeoDa/DSL.lean` generates a model's *definition* from its
   equation. Generating the *statements* that usually follow — the nesting, the reduced
   form — is the obvious next step, and the obstacle is that "the reduced form of this
   model" is not a syntactic operation on an equation: it needs the model to be
   *recognised*, which reintroduces the interpretation the design deliberately avoids.
   See `docs/DSL-RFC.md` §11.
4. **A GNS estimator.** `validation/benchmark/` cannot fit GNS with `θ ≠ 0` and
   `λ ≠ 0` because `spreg` has no such estimator; that entry in `SUPPORT` is empty and
   the harness raises rather than substituting something else.
5. **SAR and SEM reduced forms under `det ≠ 0`.** The GNS ones are already
   (`gnsDes_iff_reducedForm_of_det_ne_zero`, via `isUnit_iff_det_ne_zero`), and
   `GeoDa.Multiplier` derives the hypothesis from the weights for SAR and SEM; the
   theorems in `GeoDa.Weights` and `GeoDa.Design` still take `IsUnit` directly.

Already done, for the record: P0.1 `GeoDa/SpatialWeights.lean`, P0.2
`GeoDa/Multiplier.lean`, P0.3 `GeoDa/ReducedForm.lean`, P1.1 (the moment half)
`GeoDa/RandomVector.lean`, P2.1 `validation/`, P2.2 `validation/benchmark/`,
P3.1 `GeoDa/DSL.lean` + `docs/DSL-RFC.md`, P4.1 `AGENTS.md` +
`.claude/skills/geoda-lean/` + `docs/agent-tasks.md`, P4.2 `GeoDa/HeteroRho.lean` +
`docs/research-note-heterogeneous-rho.md`.

Same acceptance criteria as always: `./scripts/verify.sh` exits 0, no `sorry`, no
new axiom, new main theorems pinned in `Smoke.lean` and audited in `Axioms.lean`,
with `EXPECTED_COUNT` in `scripts/verify.sh` bumped to match.

## Open items

* **CI runs, but it starts on fewer events than you would guess.** The workflow
  triggers only on `push` to `main`/`master`, on `pull_request` and on
  `workflow_dispatch` — pushing a feature branch starts *nothing*, so use
  `gh workflow run lean.yml --ref <branch>` to exercise CI on a branch. The one
  annotation left is a Node.js 20 deprecation notice on `actions/checkout@v4`.
* **The GitHub build cache is off on purpose** (`use-github-cache: false` in
  `.github/workflows/lean.yml`). `lean-action`'s cache save archives the whole
  `.lake` tree — Mathlib's ~5.5 GB of oleans included — by piping `tar` into
  `zstdmt`, and on an `ubuntu-latest` runner that runs the disk out of space. It had
  never once produced a usable entry (every run logs
  `Cache not found for input keys: lake-Linux-X64-...`), and on 2026-10-13 it failed a
  `main` run outright with
  `zstd: error 70 : Write error : cannot write block : No space left on device`,
  which **skipped `./scripts/verify.sh` entirely** — the run was red even though
  `lake build` had just printed `Build completed successfully`. Re-enable it and that
  comes back. Little is lost: the Mathlib oleans come from `lake exe cache get`
  (which the action still runs, ~2.5 min), and only this project's own modules are
  left to compile.
* Local `./scripts/verify.sh` is the load-bearing evidence; CI is a second opinion
  on a different machine.
* **The `Validation` workflow is not verification.** It cross-checks the formulas
  numerically; `./scripts/verify.sh` is what proves them. Keep the distinction in
  anything you write. `validation/README.md` states it, and so does the top-level
  `README.md`.
* The README, this file and the sources are kept in step; when the theorems change,
  change all three together.
