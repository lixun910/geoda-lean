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

Lean: **observed to pass on the revision head**, in CI rather than locally. Remote
CI ran the full suite on `f0ee036a9647e1a1076b8793058133503e64d125`:

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
Both green runs are on `f0ee036`, and neither transfers to a later revision.

No local verification is claimed. Lean 4.35.0 is installed on the local machine,
but the executable reports `failed to locate application` in that execution
environment, so a local `./scripts/verify.sh` never ran; `lean-attempt.txt` keeps
the representative failure. CI is a second opinion on a different machine, not a
substitute for the local suite — and at this revision it is the only evidence that
a full `./scripts/verify.sh` has exited 0.

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

1. Observe passing full proof verification for the final code revision. Satisfied
   for revision `f0ee036` only (CI runs `38481135562`, `38481135556`); it must be
   re-observed for any commit that changes a proof or a statement.
2. Confirm author list, affiliations, contribution disclosure, and target venue.
3. Broaden the related-work comparison; obtain an independent domain review of
   `source-map.md` and the equation/probability distinction.
4. Freeze a reproducible release and archive the artifact. Do not cite a moving
   main branch as the final paper artifact.

No new estimator, Gaussian likelihood, distributional identification theorem,
large Monte Carlo study, or controlled agent benchmark is included in this revision.
