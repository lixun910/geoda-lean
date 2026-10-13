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

Lean: pending full `./scripts/verify.sh` on the revision. Local Lean 4.35.0
installed, but the executable reports `failed to locate application` in this
execution environment. No local proof-verification success is claimed.
The user authorized uploading this draft on 2026-10-13. Remote CI verification
is pending; results will be recorded once observed.

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

1. Observe passing full proof verification for the final code revision.
2. Confirm author list, affiliations, contribution disclosure, and target venue.
3. Broaden the related-work comparison; obtain an independent domain review of
   `source-map.md` and the equation/probability distinction.
4. Freeze a reproducible release and archive the artifact. Do not cite a moving
   main branch as the final paper artifact.

No new estimator, Gaussian likelihood, distributional identification theorem,
large Monte Carlo study, or controlled agent benchmark is included in this revision.
