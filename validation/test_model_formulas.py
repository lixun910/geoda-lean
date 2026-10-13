"""Numerical cross-checks of the GeoDa-Lean model formulas.

What these tests are, and are not
---------------------------------

Lean *verifies* the identities. `./scripts/verify.sh` builds every module, checks
that no proof uses `sorry`, and audits the axioms of every main theorem. That is the
verification.

These tests do something different and weaker: they compute the *same* formulas a
second time, with NumPy/SciPy linear solves and with PySAL `spreg`'s data-generating
processes, and check that the answers agree. Passing them is evidence that the
formulas have been read correctly and that they coincide with what a real
implementation computes. It is **not** a proof, and it does not substitute for
`./scripts/verify.sh`.

The first test below runs the single instance that `GeoDaTest/Smoke.lean` proves
outright, so that the Lean proof and the Python computation meet on the same
numbers.
"""

import numpy as np
import pytest
from numpy.linalg import LinAlgError

from geoda_reference import (
    gns_reduced,
    row_standardize,
    sar_reduced,
    sdm_reduced,
    sem_reduced,
    spatial_multiplier,
    structural_residuals,
    to_pysal_W,
)

# Exact arithmetic in NumPy is not exact; the reference formulas are well conditioned
# in every test below unless it says otherwise, so this tolerance is far above the
# accumulated round-off and far below any modelling difference.
TOL = 1e-10


# --------------------------------------------------------------------------------------
# The instance Lean proves outright
# --------------------------------------------------------------------------------------

# GeoDaTest/Smoke.lean, `wswap_gns_reducedForm_values`:
#   W = Wswap = [[0,1],[1,0]], X = [[1],[2]], beta = [3], theta = [-1], eps = [1,1],
#   rho = lam = 1/2, so A = B = I - (1/2)Wswap with inverse WswapInv.
# The Lean theorem `wswap_gns_reducedForm_values` proves, by `norm_num`, that the
# reduced form gives u = [2, 2] and y = [26/3, 34/3].
WSWAP = np.array([[0.0, 1.0], [1.0, 0.0]])
X2 = np.array([[1.0], [2.0]])
BETA = np.array([3.0])
THETA = np.array([-1.0])
EPS = np.array([1.0, 1.0])


def test_lean_golden_instance_gns_reduced_form():
    """The GNS reduced form on the exact instance Lean proves.

    Lean: `GeoDa.gnsDes_iff_reducedForm` + `GeoDaTest.wswap_gns_reducedForm_values`.
    """
    u, y = gns_reduced(WSWAP, 0.5, 0.5, X2, BETA, THETA, EPS)
    assert np.allclose(u, [2.0, 2.0], atol=TOL)
    assert np.allclose(y, [26.0 / 3.0, 34.0 / 3.0], atol=TOL)


def test_lean_golden_instance_satisfies_the_structural_equations():
    """And that pair really does solve the structural GNS system.

    Lean: the `mpr` half of `GeoDa.gnsDes_iff_reducedForm` -- the direction that
    says the reduced form has not dropped a solution.
    """
    u, y = gns_reduced(WSWAP, 0.5, 0.5, X2, BETA, THETA, EPS)
    ry, ru = structural_residuals(WSWAP, 0.5, 0.5, X2, BETA, THETA, EPS, u, y)
    assert np.allclose(ry, 0.0, atol=TOL)
    assert np.allclose(ru, 0.0, atol=TOL)


def test_lean_golden_instance_normalization():
    """Row standardization, including the island convention.

    Lean: `GeoDa.normalize`, `GeoDa.island_normalize`, and the values computed in
    `GeoDaTest.normalize_wpos` (`!![1/3, 2/3; 3/7, 4/7]`) and
    `GeoDaTest.normalize_wisland` (`Wisland` unchanged).
    """
    # GeoDaTest.Wpos = !![1, 2; 3, 4] -> !![1/3, 2/3; 3/7, 4/7]
    assert np.allclose(
        row_standardize(np.array([[1.0, 2.0], [3.0, 4.0]])),
        [[1.0 / 3.0, 2.0 / 3.0], [3.0 / 7.0, 4.0 / 7.0]],
        atol=TOL,
    )
    # GeoDaTest.Wisland = !![0, 0; 1, 0]: the zero row stays a zero row.
    assert np.allclose(
        row_standardize(np.array([[0.0, 0.0], [1.0, 0.0]])),
        [[0.0, 0.0], [1.0, 0.0]],
        atol=TOL,
    )
    # `libpysal`'s row standardization agrees on both, islands included.
    for W in (np.array([[1.0, 2.0], [3.0, 4.0]]), np.array([[0.0, 0.0], [1.0, 0.0]])):
        assert np.allclose(to_pysal_W(W).full()[0], row_standardize(W), atol=TOL)


# --------------------------------------------------------------------------------------
# The reduced form really is the reduced form
# --------------------------------------------------------------------------------------


def _random_instance(seed, n=5, k=2, rho=0.4, lam=0.3, row_standard=True):
    """A small well-conditioned instance. `row_standard=True` matches the Lean
    `GeoDa.RowStochastic` convention; the weights are built from a fixed pattern so
    that no row is an island. `|rho|, |lam| < 1` is the `GeoDa.Multiplier` regime."""
    rng = np.random.default_rng(seed)
    A = (rng.random((n, n)) < 0.5).astype(float)
    np.fill_diagonal(A, 0.0)
    A[A.sum(axis=1) == 0.0, 1] = 1.0  # no islands here
    W = row_standardize(A) if row_standard else A
    X = rng.normal(size=(n, k))
    return W, X, rng.normal(size=k), rng.normal(size=k), rng.normal(size=n), rho, lam


@pytest.mark.parametrize("seed", range(8))
def test_reduced_form_solves_the_structural_system(seed):
    """`(u, y)` from the reduced form satisfies both structural GNS equations.

    Lean: `GeoDa.gnsDes_iff_reducedForm`, `mpr` direction, `GeoDa.GNSDes`.
    """
    W, X, beta, theta, eps, rho, lam = _random_instance(seed)
    u, y = gns_reduced(W, rho, lam, X, beta, theta, eps)
    ry, ru = structural_residuals(W, rho, lam, X, beta, theta, eps, u, y)
    assert np.allclose(ry, 0.0, atol=TOL)
    assert np.allclose(ru, 0.0, atol=TOL)


@pytest.mark.parametrize("seed", range(8))
def test_reduced_form_is_the_only_solution(seed):
    """`A` and `B` are invertible, so the structural system has exactly one solution.

    Lean: `GeoDa.gnsDes_iff_reducedForm`, `mp` direction -- injectivity of
    `1 - ρW` gives uniqueness (`GeoDa.mulVec_injective_one_sub_smul`).
    """
    W, X, beta, theta, eps, rho, lam = _random_instance(seed)
    A = spatial_multiplier(W, rho)
    B = spatial_multiplier(W, lam)
    assert np.linalg.matrix_rank(A) == W.shape[0]
    assert np.linalg.matrix_rank(B) == W.shape[0]
    # A different "reduced form" fails the structural equations.
    u, y = gns_reduced(W, rho, lam, X, beta, theta, eps)
    ry, ru = structural_residuals(W, rho, lam, X, beta, theta, eps, u + 1e-3, y)
    assert not np.allclose(ry, 0.0, atol=TOL)


@pytest.mark.parametrize("seed", range(5))
def test_gns_restrictions_are_sar_sem_sdm(seed):
    """GNS with coefficients switched off is exactly SAR / SEM / SDM.

    Lean: `GeoDa.gnsDes_iff_sarDes`, `GeoDa.gnsDes_iff_semDes`,
    `GeoDa.gnsDes_iff_sdmDes`.
    """
    W, X, beta, theta, eps, rho, lam = _random_instance(seed)

    # lam = 0 and theta = 0 -> SAR, with u = ε.
    u, y = gns_reduced(W, rho, 0.0, X, beta, np.zeros_like(theta), eps)
    assert np.allclose(u, eps, atol=TOL)
    assert np.allclose(y, sar_reduced(W, rho, X, beta, eps), atol=TOL)

    # rho = 0 and theta = 0 -> SEM.
    u, y = gns_reduced(W, 0.0, lam, X, beta, np.zeros_like(theta), eps)
    assert np.allclose(u, sem_reduced(W, lam, X, beta, eps)[0], atol=TOL)
    assert np.allclose(y, sem_reduced(W, lam, X, beta, eps)[1], atol=TOL)

    # lam = 0 -> SDM, where B = I and u = ε.
    u, y = gns_reduced(W, rho, 0.0, X, beta, theta, eps)
    assert np.allclose(u, eps, atol=TOL)
    assert np.allclose(y, sdm_reduced(W, rho, X, beta, theta, eps), atol=TOL)


@pytest.mark.parametrize("seed", range(5))
def test_sar_and_sem_are_not_observationally_equivalent(seed):
    """SAR and SEM reduced forms are *not* the same function of `(Xβ, ε)` in general.

    Lean: `GeoDa.reducedForm_eq_iff_inverse_eq_one` -- they agree for all `(Xβ, ε)`
    exactly when both inverses collapse to the identity. Here `ρW ≠ 0` and
    `λW ≠ 0`, so they must differ.

    This is the numerical shadow of the point the Lean docstrings keep making: a SEM
    is a SAR only with *spatially filtered* regressors
    (`semMat_iff_reducedForm_of_rowSubstochastic`, `sem_reducedForm_eq_sar...`).
    """
    W, X, beta, _, eps, rho, lam = _random_instance(seed)
    y_sar = sar_reduced(W, rho, X, beta, eps)
    y_sem = sem_reduced(W, lam, X, beta, eps)[1]
    assert not np.allclose(y_sar, y_sem, atol=TOL)


# --------------------------------------------------------------------------------------
# Cross-checks against PySAL `spreg`'s DGPs
# --------------------------------------------------------------------------------------

spreg = pytest.importorskip("spreg", reason="PySAL spreg is required for the DGP cross-checks")
from spreg.dgp import dgp_gns, dgp_lag, dgp_lagerr, dgp_spdurbin, dgp_sperror  # noqa: E402


def _col(v):
    return np.asarray(v, dtype=float).reshape(-1, 1)


@pytest.mark.parametrize("seed", range(5))
def test_spreg_dgp_gns_matches_the_reference_formula(seed):
    """`spreg.dgp_gns` computes exactly the Lean reduced form.

    `dgp_gns` does `u1 = (I - λW)⁻¹u`, `y1 = xb + wxg + u1`, `y = (I - ρW)⁻¹y1` --
    which is `GeoDa.ReducedForm`'s theorem transcribed. `imethod="true_inv"` asks it
    for the exact inverse rather than the truncated series, so the two agree to
    round-off.
    """
    W, X, beta, theta, eps, rho, lam = _random_instance(seed)
    w = to_pysal_W(W)
    Wd = w.full()[0]
    assert np.allclose(Wd, W, atol=TOL)

    y_spreg = dgp_gns(
        _col(eps), _col(X @ beta), _col((W @ X) @ theta), w,
        rho=rho, lam=lam, model="sar", imethod="true_inv",
    )
    _, y = gns_reduced(W, rho, lam, X, beta, theta, eps)
    assert np.allclose(y_spreg.ravel(), y, atol=1e-8)


@pytest.mark.parametrize("seed", range(5))
def test_spreg_dgp_lag_and_sperror_match_sar_and_sem(seed):
    """The SAR and SEM DGPs agree with the corresponding Lean reduced forms.

    Lean: `GeoDa.sarMat_iff_reducedForm`, `GeoDa.semMat_iff_reducedForm`.
    """
    W, X, beta, _, eps, rho, lam = _random_instance(seed)
    w = to_pysal_W(W)
    xb = X @ beta

    y_lag = dgp_lag(_col(eps), _col(xb), w, rho=rho, imethod="true_inv")
    assert np.allclose(y_lag.ravel(), sar_reduced(W, rho, X, beta, eps), atol=1e-8)

    y_err = dgp_sperror(_col(eps), _col(xb), w, lam=lam, model="sar", imethod="true_inv")
    assert np.allclose(y_err.ravel(), sem_reduced(W, lam, X, beta, eps)[1], atol=1e-8)


@pytest.mark.parametrize("seed", range(3))
def test_spreg_dgp_spdurbin_matches_sdm(seed):
    """SDM is GNS with `λ = 0`; `dgp_spdurbin` agrees with `GeoDa.sdmDes_iff_reducedForm`."""
    W, X, beta, theta, eps, rho, _ = _random_instance(seed)
    w = to_pysal_W(W)
    y_spreg = dgp_spdurbin(
        _col(eps), _col(X @ beta), _col((W @ X) @ theta), w, rho=rho, imethod="true_inv"
    )
    assert np.allclose(y_spreg.ravel(), sdm_reduced(W, rho, X, beta, theta, eps), atol=1e-8)


@pytest.mark.parametrize("seed", range(3))
def test_spreg_dgp_lagerr_matches_gns_with_equal_error_and_lag_weights(seed):
    """`dgp_lagerr` is GNS with `θ = 0`: a spatial lag *and* a spatial error."""
    W, X, beta, theta0, eps, rho, lam = _random_instance(seed)
    w = to_pysal_W(W)
    y_spreg = dgp_lagerr(_col(eps), _col(X @ beta), w, rho=rho, lam=lam, imethod="true_inv")
    _, y = gns_reduced(W, rho, lam, X, beta, theta0 * 0.0, eps)
    assert np.allclose(y_spreg.ravel(), y, atol=1e-8)


def test_spreg_default_power_exp_is_a_truncated_neumann_series():
    """`spreg`'s *default* `imethod="power_exp"` is a truncated power expansion, so
    it is only as accurate as the Neumann series is convergent.

    Lean: `GeoDa.isUnit_one_sub_smul_of_rowSubstochastic` -- for nonnegative
    row-substochastic `W` and `|ρ| < 1` the series converges, because `‖W *ᵥ v‖ ≤ ‖v‖`
    (`GeoDa.norm_mulVec_le`) makes the terms shrink like `|ρ|ᵏ`. So this test pins down
    *why* the default is safe here, and shows the error behaving as the contraction
    predicts: it grows as `|ρ|` approaches `1`.

    `true_inv` is used everywhere else in this file precisely to avoid conflating the
    truncated series' error with a disagreement about the formula.
    """
    rng = np.random.default_rng(0)
    W, X, beta = WSWAP, X2, BETA
    eps = rng.normal(size=2)
    errors = []
    for rho in (0.2, 0.5, 0.8, 0.95):
        w = to_pysal_W(W)
        y_series = dgp_gns(
            _col(eps), _col(X @ beta), _col((W @ X) @ np.zeros(1)), w,
            rho=rho, lam=0.0, model="sar", imethod="power_exp",
        )
        y_exact = sar_reduced(W, rho, X, beta, eps)
        errors.append(np.max(np.abs(y_series.ravel() - y_exact)))
    assert errors[0] < 1e-9, errors
    # The error is not monotone by accident: it grows with |rho|, as |rho|^k does.
    assert errors[-1] > errors[-2] > errors[0], errors


# Note on `model="ma"`: `dgp_gns(..., model="ma")` uses a *moving-average* error,
# `u1 = u + λWu`, which is **not** the GNS error process this repository formalizes.
# There is no Lean counterpart, so it is deliberately not tested here rather than
# silently mapped onto `u = λWu + ε`.


# --------------------------------------------------------------------------------------
# Degenerate cases
# --------------------------------------------------------------------------------------


def test_island_weights_are_still_invertible_below_one():
    """An island row is not a problem: substochasticity is enough.

    Lean: `GeoDa.isUnit_one_sub_smul_of_rowSubstochastic` covers `GeoDa.Island`
    weights, and `GeoDaTest.wisland_rowSubstochastic` shows `Wisland` is one.
    """
    Wisland = np.array([[0.0, 0.0], [1.0, 0.0]])
    assert np.allclose(row_standardize(Wisland), Wisland, atol=TOL)  # already normalized
    for rho in (0.0, 0.3, 0.9, -0.9):
        A = spatial_multiplier(Wisland, rho)
        assert np.linalg.matrix_rank(A) == 2
    eps = np.array([1.0, 1.0])
    u, y = gns_reduced(Wisland, 0.5, 0.5, X2, BETA, THETA, eps)
    assert np.all(np.isfinite(u)) and np.all(np.isfinite(y))


def test_invertibility_fails_at_the_stability_boundary():
    """At `ρ = 1` the multiplier `I - ρW` is singular for a row-stochastic `W`.

    `GeoDa.Multiplier` proves invertibility only for `|ρ| < 1`; this test shows the
    hypothesis is not slack. For `W = WSWAP` (row sums `1`), `I - W` has a zero
    eigenvalue, so the reduced form does not exist.
    """
    A = spatial_multiplier(WSWAP, 1.0)
    assert np.linalg.matrix_rank(A) < 2
    with pytest.raises(LinAlgError):
        np.linalg.solve(A, np.array([1.0, 1.0]))


def test_nonnegativity_and_substochasticity_are_both_needed():
    """The two hypotheses of `GeoDa.isUnit_one_sub_smul_of_rowSubstochastic` are
    not decorative, and `|ρ| < 1` alone is not enough.

    Lean: `GeoDaTest.wtwo_not_isUnit` (`2 • 1` is nonnegative with row sums `2`, and
    `1 - (1/2)·2·1 = 0`) and `GeoDaTest.wneg_not_isUnit` (`!![2, -1; 0, 0]` is
    row-substochastic with a negative entry, and `I - (1/2)W` is singular).
    """
    W_two = 2.0 * np.eye(2)  # nonnegative, row sums 2, not row-substochastic
    assert np.allclose(spatial_multiplier(W_two, 0.5), 0.0, atol=TOL)

    W_neg = np.array([[2.0, -1.0], [0.0, 0.0]])  # row sums 1 and 0, but a negative entry
    assert np.allclose(np.abs(spatial_multiplier(W_neg, 0.5)).sum(axis=1).max(), 1.0)
    assert np.linalg.matrix_rank(spatial_multiplier(W_neg, 0.5)) < 2
