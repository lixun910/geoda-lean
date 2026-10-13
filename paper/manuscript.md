# GeoDa-Lean: A Machine-Checked Foundation for Spatial Regression Model Specifications

**Working manuscript — 13 October 2026.** Author list and affiliations to be confirmed. This draft describes a formalization artifact, not a new spatial estimator. Artifact validation status and the exact revision are recorded separately in [verification.md](verification.md).

## Abstract

Spatial regression models combine feedback in outcomes, dependence in disturbances, and spatially lagged regressors. Their familiar matrix notation can conceal distinctions between structural equations, reduced-form maps, probability distributions, and numerical algorithms. We present GeoDa-Lean, a Lean 4 library that makes these distinctions explicit for a finite-dimensional family centered on the general nesting spatial model. The development connects abstract linear operators, concrete spatial weights, and design-matrix specifications; proves model restrictions and two-way reduced-form equivalences; derives multiplier invertibility from nonnegative row-substochastic weights; and establishes first- and second-moment identities under explicit integrability assumptions. A small Lean-native command generates inspectable model definitions, with definitional-equality checks against handwritten specifications. Case studies cover latent-disturbance bookkeeping, islands, an incorrect interpretation of column normalization, and an implementation guard that rejects a convergent power expansion. Numerical comparisons with PySAL provide separate implementation evidence. The contribution is a reusable, auditable organization of established mathematics, with explicit boundaries on what its proofs establish. It does not verify floating-point estimators, statistical identification, likelihoods, or the productivity of AI-assisted research.

**Keywords:** spatial regression; formalization; Lean 4; model specification; spatial weights; reproducibility

## 1. Introduction

Consider a researcher who asks a coding assistant to extend a spatial regression model and derive its reduced form. A plausible answer may conceal several errors: an omitted latent-variable constraint, an inverse used without a nonsingularity hypothesis, a covariance with the wrong matrix order, or a claim of statistical identification supported only by a deterministic algebraic calculation. Numerical examples alone cannot establish the universal statements involved. Conversely, a machine-checked proof cannot decide whether its formal statement captures the intended statistical question.

GeoDa-Lean addresses the intervening specification layer. It represents model equations as propositions and places each assumption at the theorem that needs it. Restrictions can therefore be checked without importing unnecessary probability assumptions, while probability results require their own explicit moment conditions. The intended use is to support researchers and coding agents in constructing and reviewing model specifications before developing estimators.

The mathematical ingredients are established. We do not claim new spatial models or new econometric theory. We instead contribute: (i) a compositional formalization connecting equations, weights, inverse operators, and moments; (ii) a traceable specification interface with ordinary Lean semantics; and (iii) case studies showing why proof correctness, specification fidelity, and numerical behavior need separate evidence. The artifact includes counterexamples to overgeneralized assumptions and tests of generated definitions. The number of declarations is an audit statistic, not a measure of mathematical novelty.

## 2. Background and relation to existing work

Anselin, Serenini, and Amaral's June 2024 manuscript organizes spatial regression specifications by the inclusion of spatial lags of outcomes, covariates, and disturbances [1, §2]. We use this classification as a specification reference, not as evidence that its estimation or model-selection procedures have been formalized. In particular, our results do not establish the validity of selection tests.

LeSage's discussion of SDEM and SDM supplies a second source for the focused reproduction case [2, pp. 16–20]. Its distributional and weights conventions are stronger than several hypotheses needed for our algebraic identities. These differences are recorded explicitly rather than silently transferring a model name between unequal specifications.

Lean 4 provides an extensible language whose elaborated declarations and proof terms are checked by a kernel [3]. Mathlib supplies the matrix, algebra, norm, and integration infrastructure [4]. Our contribution is the domain-specific arrangement and connection of these ingredients, not a new proof calculus or a replacement for Mathlib. PySAL's pinned `spreg` implementation is an independently maintained numerical comparison target [5]. The comparison concerns selected data-generating formulas and does not verify PySAL itself.

This draft does not claim to be the first formalization of spatial econometrics. A broader related-work review of formalized statistics, scientific models, and numerical verification remains a submission task. Likewise, the development's use of AI tools is provenance, not an evaluated advantage over human formalization.

## 3. Scope and mathematical representation

Let (n,k\in\mathbb N), (W\in\mathbb R^{n\times n}), (X\in\mathbb R^{n\times k}), and (\beta,\theta\in\mathbb R^k). All these quantities, and the scalar coefficients (\rho,\lambda), are deterministic. We write

\[
c=X\beta+WX\theta,\qquad M_\rho=I-\rho W,\qquad M_\lambda=I-\lambda W.
\]

The structural GNS specification is

\[
y=\rho Wy+X\beta+WX\theta+u,\qquad u=\lambda Wu+\varepsilon. \tag{1}
\]

The core representation uses `Vec n := Fin n → ℝ` and square real matrices for weights. The design layer forms the products explicitly. Earlier layers instead accept an arbitrary linear endomorphism or supplied vectors `xb` and `wxθ`. Bridge theorems show how these representations agree; the general supplied-vector results do not impose that a vector lie in the column space of a fixed design.

Equation (1) is a proposition about vectors, not a probability distribution. Normality, independence, rank, symmetry, diagonal zeros, and row normalization are not implicit parts of it. The algebra is valid for arbitrary finite dimensions, including degenerate dimensions allowed by Lean; it does not suggest that every such instance is an estimable statistical model.

A practical specification detail concerns intercepts. Our coefficient vectors have the same length, and every design column may appear in (WX\theta). Empirical specifications often exclude a lagged intercept. One can represent that convention by constraining the corresponding entry of (\theta) to zero. For row-stochastic weights a constant column is unchanged by the lag, so allowing both intercept coefficients can create redundancy. No rank or identification result is inferred from the general definition.

### 3.1 Restrictions and latent variables

The following restrictions are supported by named model relations in the artifact:

| Restricted GNS parameters | Resulting specification | Latent-variable condition retained |
|---|---|---|
| (\lambda=0,\theta=0) | SAR | (u=\varepsilon) |
| (\rho=0,\theta=0) | SEM | Error equation retained |
| (\lambda=0) | SDM | (u=\varepsilon) |
| (\rho=0,\lambda=0) | SLX | (u=\varepsilon) |
| (\rho=0) | SDEM | Error equation retained |

For example, `gnsDes_iff_sarDes` relates the restricted GNS proposition to **SAR together with** (u=\varepsilon). Dropping the second conjunct while leaving (u) free would change the proposition. If one instead existentially quantified the latent disturbance, a different theorem statement would be appropriate. This distinction is a small but instructive example of specification work that informal model diagrams often suppress.

### 3.2 Spatial weights and islands

`Nonneg W` expresses entrywise nonnegativity. `RowSubstochastic W` expresses the row-sum upper bound, separately from nonnegativity. `RowStochastic W` expresses row sums equal to one. These names must be read with their definitions: the row predicates alone do not constrain entry signs. An island is an identically zero row, and `ZeroDiag W` expresses a separate condition.

Row normalization divides a row by its sum. Lean's real inverse is totalized at zero, so a zero row remains zero. Under nonnegativity this agrees with the intended island convention. Without nonnegativity, a nonzero row can have zero sum and be mapped to zero; the unrestricted algebraic normalization result must not be confused with a claim that all such matrices are appropriate spatial weights.

## 4. Reduced forms and sufficient invertibility conditions

### 4.1 Two-way elimination

If both multipliers are invertible, write (A=M_\rho^{-1}) and (B=M_\lambda^{-1}). The formal reduced-form theorem establishes

\[
\operatorname{GNS}(y,u,\varepsilon)
\iff
\left[u=B\varepsilon\ \land\ y=A(c+B\varepsilon)\right]. \tag{2}
\]

Both the forward and reverse implications matter. Substitution checks that the displayed pair solves the structural equations, while multiplication by inverses shows that every solution is that pair. Thus the characterization entails existence and uniqueness of ((u,y)) for fixed inputs. The library presents this through an equivalence rather than requiring a separate existence-and-uniqueness declaration.

`gnsDes_iff_reducedForm_of_inverse` takes two-sided inverse equations. Wrappers use `IsUnit` in the matrix ring or nonzero determinants. This keeps the elementary algebra reusable and makes the nonsingularity obligation visible. The totalized inverse operation alone would not justify a solution formula at a singular matrix. A nonzero determinant is an exact mathematical condition; it is not a floating-point conditioning test.

### 4.2 Row bounds

For entrywise nonnegative weights with row sums at most one,

\[
\|Wv\|_\infty\leq\|v\|_\infty.
\]

If (M_\rho v=0), then (v=\rho Wv), and hence

\[
\|v\|_\infty\leq |\rho|\,\|v\|_\infty.
\]

Under (|\rho|<1), this forces (v=0). Finite-dimensional linear algebra yields invertibility. The proof avoids a spectral decomposition, symmetry, and a matrix operator-norm instance. The same argument applies to (\lambda), and zero rows are allowed.

The hypotheses constitute a sufficient condition, not a necessary characterization for each matrix. For example, (W=0) gives an invertible multiplier for every scalar. Two existing finite counterexamples show why neither nonnegativity nor the row bound can simply be removed from this uniform theorem: (W=2I,\rho=1/2) gives the zero multiplier; and (W=\begin{pmatrix}2&-1\\0&0\end{pmatrix},\rho=1/2) satisfies the row-sum bound but gives a singular multiplier.

### 4.3 Column bounds and the interpretation gap

Nonnegative column-substochastic weights make (W^T) nonexpansive in the infinity norm. They also imply invertibility of **both** (I-\rho W^T) and (I-\rho W) for (|\rho|<1), because transposition preserves invertibility. The revision adds `isUnit_one_sub_smul_of_colSubstochastic` (verification pending) as a corollary of the existing transpose result.

The earlier task narrative incorrectly described the untransposed conclusion as false. The checked theorem was narrower and correct; the error was in its prose interpretation. This case illustrates a limit of kernel checking: it verifies the statement actually submitted, not every explanation around it.

## 5. Probability layer and the structural bridge

On a probability space ((\Omega,\mu)), random vectors are functions (\Omega\to\mathbb R^n). Expectation and covariance are defined coordinatewise using integrals. `HasMoments` requires integrability of each coordinate and each coordinate product. `IsWhiteNoise` adds zero mean and covariance (\sigma^2I). Here `σ2` is a real-valued parameter constrained through those moment equalities; the definition does not separately require strict positivity. It does not assert Gaussianity or independence.

The reusable affine result is

\[
\mathbb E[C\varepsilon+d]=d,\qquad
\operatorname{Cov}(C\varepsilon+d)=\sigma^2 CC^T. \tag{3}
\]

Applying it to (2) gives

\[
\begin{aligned}
\mathbb E[u]&=0,&\operatorname{Cov}(u)&=\sigma^2BB^T,\\
\mathbb E[y]&=Ac,&\operatorname{Cov}(y)&=\sigma^2(AB)(AB)^T.
\end{aligned} \tag{4}
\]

The product order is retained throughout; no commutativity assumption is needed to derive these identities. Generic theorems such as `gns_moments` accept matrices (A,B). Their names alone do not enforce that the arguments are spatial multipliers.

The revision therefore adds `gnsDes_moments_of_rowSubstochastic` (verification pending). Its premises include the weights bounds, (|\rho|<1), (|\lambda|<1), white-noise moments, and the structural GNS equations at every sample point. Its proposed proof obtains the reduced-form equalities, rewrites the random functions, and applies the generic moment theorem. This provides one citable statement connecting the modeling assumptions to (4). The pointwise premise is explicit and stronger than an almost-everywhere structural equation; the current bridge does not silently claim the more general version.

## 6. Specification syntax and assurance boundaries

The `spatial_model` command accepts typed binders and an equation and elaborates a proposition-valued definition. For example:

```lean
spatial_model MySAR (n k : ℕ) (W : WMat n) (X : DMat n k)
    (y : Vec n) (β : Vec k) (ε : Vec n) (ρ : ℝ) :
  y = ρ • (W *ᵥ y) + X *ᵥ β + ε
```

This is intentionally small. It does not infer a model class, synthesize an estimator, or decide which hypotheses make a requested property true. Undeclared parameters and non-propositional bodies are rejected by the command's checks and Lean elaboration. Selected generated definitions are compared with handwritten specifications using definitional equality (`rfl`), and rejection cases are tested.

The command adds no proof oracle. Nevertheless, kernel acceptance of a generated definition does not establish that the input expresses a researcher's intention. The handwritten comparison, source map, and human review remain specification checks. Existing named `#check` entries ensure declarations remain available and elaboratable; they are not by themselves automated locks on exact types. Changes to statements still require review of the source diff.

The assurance boundary can be summarized as follows:

| Evidence | Establishes | Does not establish |
|---|---|---|
| Lean proof and axiom audit | Formal proposition follows under its hypotheses | Correct interpretation of a source or research question |
| DSL definitional-equality test | Tested generated definition equals the reference definition | Fidelity of arbitrary future specifications |
| Full-text source mapping | Reviewed passages match the stated mathematical scope | Complete formalization of the source's statistical theory |
| Numerical comparison | Selected implementations agree on tested instances and tolerances | Universal correctness or verified floating-point error bounds |
| Historical agent task record | A documented development example | Controlled productivity or model-discovery evidence |

## 7. Case studies and numerical evidence

### 7.1 SDEM as a reuse case

SDEM combines lagged covariates with an autoregressive disturbance. Its formalization reuses the GNS restriction at (\rho=0), the SEM inverse calculation, and the affine moment layer. Setting (\lambda=0) leaves SLX with (u=\varepsilon); setting (\theta=0) leaves SEM. These are equation-level relations. The source's infinite-series discussion is not represented by the inverse theorem alone, and the repository does not formalize spillover derivatives.

The original agent exercise used pre-existing related proofs and source-search results. It is therefore an assembly and reuse example, not a blind discovery benchmark. Subsequent full-text review of the relevant source passages improves semantic traceability without changing that historical limitation.

### 7.2 Numerical agreement and a conservative stopping guard

The revised SDEM tests explicitly set `rtol=0.0`; absolute thresholds are (10^{-10}) for internal comparisons and (10^{-8}) for `spreg` comparisons. In ten fixed-seed SDEM comparisons—six ordinary instances and four with islands—the maximum absolute discrepancy was (8.881784197001252\times10^{-16}). Both implementations use floating-point arithmetic. `imethod="true_inv"` denotes a numerical inverse, not an exact-arithmetic oracle. Environment versions and per-case errors are recorded in `numerical-evidence.json`.

The same fixture at (\lambda=0.99) triggers `spreg 1.9.1`'s power-expansion error. Inspection of the installed source shows a guard that raises when consecutive increment norms increase. For this column-vector input the norm is Euclidean. Nonnegative row-substochasticity controls the infinity norm; it does not prohibit transient Euclidean growth for a nonsymmetric matrix. Thus the implementation's rejection does not contradict the sufficient invertibility theorem or establish divergence. The evidence script records the first increase and both norms. The library does not currently prove a Neumann-series theorem or an error bound for this implementation.

The complete existing Python suite passes after the tolerance revision (95 tests). We report that result as a numerical and harness check. We do not use the repository's small Monte Carlo smoke study to argue estimator superiority, infer asymptotic behavior, or explain estimation bias by proximity to an invertibility bound.

### 7.3 Algebraic recovery versus statistical identification

The heterogeneous-coefficient extension replaces (\rho W) by (\operatorname{diag}(r)W). If every row contains a nonzero entry, equality of the complete reduced-form maps for all supplied deterministic vectors and innovations implies equality of (r). An island's coefficient, in contrast, multiplies a zero row and leaves the map unchanged.

The positive result is algebraic map injectivity. It does not prove that equality of observable distributions at a fixed design identifies the parameter. Treating the universal input-map premise as a distributional premise would overstate the result. We retain existing declaration names for compatibility but use the narrower terminology in this manuscript. The island result also concerns observation-specific coefficients, not a general failure of identification for the single SDEM error coefficient.

## 8. Reproducibility and provenance

The development pins Lean `v4.35.0`, Mathlib commit `56a005855ea17e0b0958f73ec801ae140b0a1679`, and the direct numerical dependencies. `scripts/verify.sh` builds the library and tests, rejects placeholder proofs, and audits designated results against the standard axiom footprint `propext`, `Classical.choice`, and `Quot.sound`. This is a conditional formal guarantee within Lean's foundations, not an axiom-free result. Its selected-declaration audit is not a substitute for statement review.

The reviewed baseline is repository commit `eb53ae67cf062cfe7481a853810ce9c084a79ba6`. The revision adds two audited results to the baseline list of 115. Final validation status belongs to the exact revision identified in `verification.md`; a successful earlier build must not be transferred to a changed proof. The replication instructions separate proof checking from numerical checks.

Repository provenance records that the baseline proofs were produced with Claude. The present Paper 1 revision was prepared with Codex, including the two proposed bridge/corollary proofs and the editorial audit. These records do not measure autonomous success, human effort, or productivity. Author responsibility for the specification, interpretation, and final manuscript remains a separate matter.

## 9. Limitations and future work

The library is limited to finite-dimensional, deterministic-weight specifications and a coordinatewise moment layer. It does not verify Gaussian laws, likelihoods, statistical identification, estimator consistency, asymptotic distributions, matrix conditioning, or floating-point solvers. A generic algebraic GNS envelope need not be a well-identified empirical specification. Model inclusion does not validate fitting the largest model.

The numerical evidence covers small selected instances. It can expose implementation conventions and discrepancies, but not certify a numerical implementation. Formal series convergence and truncation bounds would be useful separate extensions. Almost-everywhere structural hypotheses would broaden the probability interface. Generalizing the single-weight design to distinct lag, covariate, and error weights would require an explicit interface change.

A more ambitious AI-assisted discovery study should use held-out tasks, prespecified assumptions, recorded interventions, and comparisons against suitable baselines. None of those claims is needed for the present library contribution. Before submission, the literature comparison must be broadened and the source-to-theorem map reviewed by a spatial econometrician. This draft avoids priority claims while that work remains open.

## 10. Conclusion

GeoDa-Lean makes a bounded collection of spatial regression specifications and their consequences explicit in a proof assistant. Its useful unit is a theorem with inspectable assumptions and a documented interpretation, rather than a model label or a passing simulation. The case studies show that the strongest role for formalization here is to connect reusable mathematics while making the remaining semantic and numerical obligations visible.

## References

[1] Anselin, L., Serenini, R., and Amaral, P. (2024). *Spatial Econometric Model Specification Search: Another Look*. Manuscript dated June 11, 2024. [Full text](https://brsa.org.br/wp-content/uploads/wpcf7-submissions/32125/SPATIAL-ECONOMETRIC-MODEL-SPECIFICATION-SEARCH.pdf). The version cited here is the inspected manuscript, not an inferred final publication.

[2] LeSage, J. P. (2014). What Regional Scientists Need to Know about Spatial Econometrics. *The Review of Regional Studies*, 44(1), 13–32. [Full text](https://rrs.scholasticahq.com/article/8081-what-regional-scientists-need-to-know-about-spatial-econometrics.pdf).

[3] de Moura, L., and Ullrich, S. (2021). The Lean 4 Theorem Prover and Programming Language. *Automated Deduction—CADE 28*. DOI: [10.1007/978-3-030-79876-5_37](https://doi.org/10.1007/978-3-030-79876-5_37). [Author PDF](https://lean-lang.org/papers/lean4.pdf).

[4] The mathlib Community (2020). The Lean Mathematical Library. *Proceedings of CPP 2020*. DOI: [10.1145/3372885.3373824](https://doi.org/10.1145/3372885.3373824). [Author PDF](https://leanprover-community.github.io/papers/mathlib-paper.pdf). Background reference; the artifact uses the pinned Lean 4 library revision above.

[5] PySAL developers. *spreg*, version 1.9.1. Inspected installed Python modules `spreg.dgp` and `spreg.utils`; dependency pins and source hash accompany the numerical evidence. [Project](https://github.com/pysal/spreg).
