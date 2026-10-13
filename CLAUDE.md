# Working notes for this repository

Lean 4 + Mathlib formalization of the equation-level nesting of the General
Nesting Spatial (GNS) model into SAR, SEM and SDM, with the SAR/SEM reduced
forms under an invertibility assumption.

**Status: compiler-verified.** `./scripts/verify.sh` exits 0 and audits 25 theorems.

## Layout

```
GeoDa.lean             root module (imports all three libraries)
GeoDa/GNS.lean         abstract: W is an ℝ-linear endomorphism of Fin n → ℝ
GeoDa/Weights.lean     concrete: W is Matrix (Fin n) (Fin n) ℝ, via Matrix.mulVec
GeoDa/Design.lean      design matrix X; Xβ = X *ᵥ β, WXθ = (W * X) *ᵥ θ
GeoDaTest/Smoke.lean   compile-time tests: signature pins + explicit n = 1, 2 examples
GeoDaTest/Axioms.lean  axiom audit, consumed by scripts/verify.sh
scripts/verify.sh      build + no-sorry + axiom audit
docs/original-GNS.lean the pre-existing draft, kept verbatim (see "Provenance")
README.md              the user-facing write-up; keep it in step with the code
```

## How to verify — always run this before claiming anything works

```
./scripts/verify.sh
```

It runs `lake build`, greps the sources for `sorry`/`admit`, and checks that all
25 main theorems in `GeoDaTest/Axioms.lean` depend only on
`[propext, Classical.choice, Quot.sound]`. Expected tail:

```
     ok: all 25 theorems depend only on [propext, Classical.choice, Quot.sound]
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
* `W` is an arbitrary real matrix: row standardization, symmetry and
  non-negativity are **not** assumed.
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

1. **Reduced forms under `det ≠ 0`.** The hypothesis today is `IsUnit (1 - ρ • W)`;
   connect it to `Matrix.isUnit_iff_isUnit_det` so the statements read in terms of
   the determinant, which is what an implementation actually checks.
2. **Row-standardized weights.** Prove `W ⬝ 1 = 1`-type properties and
   invertibility of `1 - ρW` for `|ρ| < 1` (Neumann series / Gershgorin radius).
   This is the first place a regularity assumption on `W` would enter; everything
   so far is assumption-free in `W`.
3. **A GNS-level reduced form.** Eliminate `u` and then `y` in GNS itself, under
   invertibility of both `1 - ρW` and `1 - λW`.
4. **Numerical cross-checks against PySAL `spreg`.** The formal objects now
   coincide with what `spreg` computes, but nothing has been compared against a
   real implementation yet.

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
* The README, this file and the sources are kept in step; when the theorems change,
  change all three together.
