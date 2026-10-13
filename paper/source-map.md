# Source-to-theorem map

Reviewed 2026-10-13. “Reviewed” means the specified full-text passages were read;
it does not mean every page of every source was studied. References below use the
numbering in `manuscript.md`. Repository paths are relative to the root.

## Literature anchors

| Source location | Mathematical item | Repository anchor | Scope difference |
|---|---|---|---|
| [1], printed p. 3, Eq. (1), and Error specification below it (PDF p. 5) | SAR and SEM equations | `GeoDa/Design.lean`: `SARDes`, `SEMDes` | Source disturbance `e` and innovation `u` map to our `u` and `ε` for SEM |
| [1], printed p. 4, SLX display; p. 5, SDM display | Lagged covariates | `SLXDes`, `SDMDes` | Lagged intercept excluded in source; set its `θ` entry to zero in our general design |
| [1], printed p. 7, §2.3, Eq. (5) (PDF p. 9) | GNS specification | `GNSDes`; restriction theorems | `γ → θ`, `e → u`, source `u → ε`; our equation-level envelope does not establish identification |
| [1], printed p. 4, Eq. (3) | Filtered-error representation | `semDes_reducedForm_eq_sarDes_reducedForm_of_filtered` | Deterministic map identity; not a full common-factor statistical test |
| [2], p. 16, Eqs. (1)–(2) | SLX and SDEM | `SLXDes`, `SDEMDes` | Source Gaussian noise, zero diagonal, normalized rows are not all needed for algebra |
| [2], p. 16, disturbance-inverse paragraph | SDEM reduced form | `sdemDes_iff_reducedForm` | Inverse identity only; source series expansion is not formalized |
| [2], p. 19, Eq. (6) and preceding paragraph | SDEM restrictions to SLX/SEM | `sdemDes_iff_slxDes_of_lam_zero`, `sdemDes_iff_semDes_of_theta_zero` | SLX equivalence explicitly retains `u = ε` |
| [3], §§1–2 | Lean's extensible proof environment | `GeoDa/DSL.lean` | Background, not evidence that this DSL matches an intended model |
| [4], abstract and library-design discussion | Reusable formal mathematics | Pinned Mathlib dependency | Historical Lean 3 paper; not documentation for the exact current API |

Source [1]: https://brsa.org.br/wp-content/uploads/wpcf7-submissions/32125/SPATIAL-ECONOMETRIC-MODEL-SPECIFICATION-SEARCH.pdf

Source [2]: https://rrs.scholasticahq.com/article/8081-what-regional-scientists-need-to-know-about-spatial-econometrics.pdf

Source [3]: https://lean-lang.org/papers/lean4.pdf

Source [4]: https://leanprover-community.github.io/papers/mathlib-paper.pdf

## Artifact-derived results

The following claims are justified by their explicit Lean statements and proofs,
not presented as transcriptions of a particular numbered literature equation.

| Manuscript claim | Exact declaration or evidence | Hypotheses / boundary |
|---|---|---|
| Two-way GNS reduced form | `GeoDa.gnsDes_iff_reducedForm_of_det_ne_zero` | Both exact determinants nonzero; both latent and outcome equations retained |
| Weights imply invertibility | `GeoDa.isUnit_one_sub_smul_of_rowSubstochastic` | `Nonneg`, row-sum bound, absolute coefficient below one |
| Column corollary | `GeoDa.isUnit_one_sub_smul_of_colSubstochastic` | Same sign/bound conditions on columns; added in this revision |
| Affine moments | `GeoDa.affine_moments`, `GeoDa.gns_moments` | Probability measure; integrable coordinates/products; white-noise moments |
| Structural-to-moment bridge | `GeoDa.gnsDes_moments_of_rowSubstochastic` | Pointwise equations, deterministic inputs, weights bounds, moment assumptions; added in revision |
| Map injectivity | `GeoDa.heteroSAR_parameter_identified` | All supplied `xb, ε`, both multipliers invertible, no zero row; not equality in law |
| Island invariance | `GeoDa.heteroSARDes_island_invariant`, `GeoDa.heteroSAR_reducedForm_island_invariant` | Observation-specific coefficient at a zero row |
| Definition fidelity | `GeoDaTest.sdemViaDsl_eq_SDEMDes` and DSL tests | Definitional equality for tested definitions |
| Numerical agreement | `validation/paper1_evidence.py`, `paper/numerical-evidence.json` | Ten SDEM fixtures, `spreg 1.9.1`, absolute error only |
| Power-expansion guard | Installed `spreg.utils.power_expansion` source; hash in JSON | Checks increment Euclidean norm growth; no formal algorithm verification |

## Deliberately unresolved source work

- The earlier heterogeneous-ρ note contains search-only references. They are not
  promoted to independently checked literature claims in this paper.
- No exact page citation is invented for the LeSage–Pace book: it was not inspected.
- The moment and norm arguments are proved in the artifact, but a broader comparison
  with formalized statistical libraries is still required for submission positioning.
- This bounded review supports the displayed model equations. It does not certify all
  estimation, impact, or identification claims in the cited publications.
