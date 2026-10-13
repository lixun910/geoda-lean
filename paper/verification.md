# Revision and validation record

Baseline: `eb53ae67cf062cfe7481a853810ce9c084a79ba6`.
Branch: `paper1-semantic-review`.

## Scope

- Two added declarations: column-substochastic original-multiplier invertibility;
  pointwise structural GNS-to-moments bridge under row-substochastic weights.
- Existing theorem statements and existing `#check` entries unchanged.
- No axioms added. No hypotheses of existing theorems added, removed, or modified.
- New bridge assumptions: probability measure; deterministic W/X/coefficients;
  entrywise nonnegative row-substochastic W; absolute rho/lambda below one;
  explicit white-noise moments; structural equations at every sample point.
- New column corollary assumptions: nonnegative column-substochastic W and |rho|<1.
- Audit list expanded from 115 to 117 results.
- SDEM allclose calls use explicit zero relative tolerance.

## Validation status

Python: 95 passed locally after the tolerance change; `python-tests.txt`.
Evidence script: ten comparisons passed; maximum absolute error
`8.881784197001252e-16`; `numerical-evidence.json`.

Lean: **observed to pass**, locally and in CI. The verification anchor is
`f0ee036a9647e1a1076b8793058133503e64d125` — the last commit of this branch that
changes a Lean source file. Every run below is on a commit whose Lean sources are
identical to the anchor's — on the branch head at the time of writing, and on later
documentation-only commits.

Locally, 2026-10-13, on macOS 26.6.2 (Darwin 25.6.0, Apple M2 Max, arm64) with Lean
4.35.0 from elan: `./scripts/verify.sh` exits 0 in 33 s, its three steps reporting

```
==> 1/3  lake build        Build completed successfully (2632 jobs).
==> 2/3  no sorry / admit  ok: no sorry/admit in any proof
==> 3/3  axiom audit       ok: all 117 theorems depend only on [propext, Classical.choice, Quot.sound]
VERIFICATION SUCCEEDED
```

That is the load-bearing evidence the repository asks for; the CI runs below are
the second opinion, on a different machine and a different architecture. In CI:

- `Lean` run `38481135562`, 2026-10-13, 1 m 58 s, green. Its
  `./scripts/verify.sh` step ends

  ```
       ok: all 117 theorems depend only on [propext, Classical.choice, Quot.sound]
  VERIFICATION SUCCEEDED
  ```

- `Validation` run `38481135556`, 2026-10-13, 43 s, green: `95 passed in 2.86s`,
  and the CI-scale Monte Carlo smoke run reports `50/50 ok, 0 failed` on every
  fixture.

The first revision commit `22ea450` did **not** verify. `Lean` run `38480834701`
went red on `error: GeoDa/Multiplier.lean:215:8: Unknown constant
'Matrix.isUnit_transpose.mp'`; `f0ee036` is the commit that replaced that proof.

The commits after `f0ee036` edit documentation only, and CI verifies them too: on
the branch head `37ce61d`, `Lean` run `38481610834` is green in 2 m 24 s with the
same tail and `Validation` run `38481610899` with it. So the verification is not
tied to a particular documentation commit, and this record is deliberately not
enumerated per prose edit — that would make the anchor chase a moving branch,
which is the thing item 4 of *Before submission* warns against. The anchor moves
only when a proof or a statement moves, and then the runs above stop applying.

`lean-attempt.txt` keeps an earlier local failure, from the session that wrote the
revision: Lean 4.35.0 installed, but the executable reporting `failed to locate
application`. That was an environment fault and not a gap in the proofs, and it
does not reproduce — the local run above is the same repository on the same pinned
toolchain. It is kept rather than deleted because a record that only ever shows the
successful attempt is the one that is not worth reading.

The user authorized uploading this draft on 2026-10-13.

## Reproduce

```sh
# With the pinned toolchain installed, from the repository root:
lake exe cache get
./scripts/verify.sh
python -m venv .venv
.venv/bin/pip install -r validation/requirements.txt
.venv/bin/python -m pytest validation -q
.venv/bin/python validation/paper1_evidence.py
```

The evidence script imports the deterministic SDEM fixtures. Numerical results
are not Lean proofs. The recorded Python dependencies are direct pins; the JSON
records runtime versions, and `python-environment.txt` records the full local
package set for this run.

## Before submission

1. Observe passing full proof verification for the final code revision. Satisfied:
   local `./scripts/verify.sh` exits 0, and CI runs `38481135562` / `38481135556`
   agree. Holds for `f0ee036` and for the documentation-only commits after it. A
   commit that changes a proof or a statement needs the observation repeated.
2. Confirm author list, affiliations, contribution disclosure, and target venue.
3. Broaden the related-work comparison; obtain an independent domain review of
   `source-map.md` and the equation/probability distinction.
4. Freeze a reproducible release and archive the artifact. Do not cite a moving
   main branch as the final paper artifact.

No new estimator, Gaussian likelihood, distributional identification theorem,
large Monte Carlo study, or controlled agent benchmark is included in this revision.
