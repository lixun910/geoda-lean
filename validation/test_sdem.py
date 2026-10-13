"""Numerical cross-check of the SDEM benchmark model against PySAL `spreg`.

`GeoDa/Sdem.lean` formalizes

    y = Xβ + WXθ + u        u = λWu + ε

and proves its reduced form, its nesting in GNS, and the two nestings LeSage (2014) states:
SDEM with `λ = 0` is SLX, and SDEM with `θ = 0` is SEM.

**This checks an implementation, not the theorems.** The Lean side is the proof. What these
tests add is that the published model is the one a reference implementation computes: the
DGP is PySAL's, not ours, so agreement is not circular.

`spreg.dgp.dgp_slxerror(u, xb, wxg, w, lam)` does `u₁ = (I − λW)⁻¹u`, `y = xb + wxg + u₁`,
which is `GeoDa.sdemDes_iff_reducedForm` transcribed into somebody else's code.
"""

import numpy as np
import pytest

from geoda_reference import row_standardize, sdem_reduced, sem_reduced, to_pysal_W

TOL = 1e-10
SPREG_TOL = 1e-8  # `spreg` goes through a sparse inverse rather than a solve

spreg = pytest.importorskip("spreg", reason="PySAL spreg is required for the DGP cross-check")
from spreg.dgp import dgp_slxerror, dgp_sperror  # noqa: E402

WSWAP = np.array([[0.0, 1.0], [1.0, 0.0]])
X2 = np.array([[1.0], [2.0]])


def _instance(seed, n=7, k=2, lam=0.4, islands=False):
    """A small row-standardized instance with the standard `Xβ` and `WXθ` slots."""
    rng = np.random.default_rng(seed)
    A = (rng.random((n, n)) < 0.45).astype(float)
    np.fill_diagonal(A, 0.0)
    A[A.sum(axis=1) == 0.0, 1] = 1.0
    if islands:
        A[0, :] = 0.0
        A[:, 0] = 0.0
    W = row_standardize(A)
    X = np.hstack([np.ones((n, 1)), rng.normal(size=(n, k - 1))])
    beta = rng.normal(size=k)
    theta = rng.normal(size=k)
    eps = rng.normal(size=n)
    return W, X, beta, theta, eps, lam


def _col(v):
    return np.asarray(v, dtype=float).reshape(-1, 1)


# --------------------------------------------------------------------------------------
# The published reduced form, against PySAL's DGP
# --------------------------------------------------------------------------------------


@pytest.mark.parametrize("seed", range(6))
def test_spreg_dgp_slxerror_matches_the_sdem_reduced_form(seed):
    """`spreg.dgp.dgp_slxerror` computes exactly `GeoDa.sdemDes_iff_reducedForm`.

    `imethod="true_inv"` asks for the exact inverse rather than the truncated series, so the
    two agree to round-off and the comparison is about the *formula*, not about a tolerance.
    """
    W, X, beta, theta, eps, lam = _instance(seed)
    w = to_pysal_W(W)
    assert np.allclose(w.full()[0], W, atol=TOL)

    y_spreg = dgp_slxerror(_col(eps), _col(X @ beta), _col((W @ X) @ theta), w,
                           lam=lam, imethod="true_inv")
    _, y = sdem_reduced(W, lam, X, beta, theta, eps)
    assert np.allclose(y_spreg.ravel(), y, atol=SPREG_TOL)


@pytest.mark.parametrize("seed", range(4))
def test_islands_do_not_break_the_dgp(seed):
    """An island row is fine here too: substochasticity is enough for invertibility, as
    `GeoDa.isUnit_one_sub_smul_of_rowSubstochastic` says."""
    W, X, beta, theta, eps, lam = _instance(seed, islands=True)
    assert np.allclose(W[0, :], 0.0)
    w = to_pysal_W(W, row_standard=False)
    y_spreg = dgp_slxerror(_col(eps), _col(X @ beta), _col((W @ X) @ theta), w,
                           lam=lam, imethod="true_inv")
    _, y = sdem_reduced(W, lam, X, beta, theta, eps)
    assert np.allclose(y_spreg.ravel(), y, atol=SPREG_TOL)


# --------------------------------------------------------------------------------------
# LeSage's two nestings, numerically
# --------------------------------------------------------------------------------------


@pytest.mark.parametrize("seed", range(4))
def test_sdem_with_lambda_zero_is_slx(seed):
    """SDEM with `λ = 0` gives `y = Xβ + WXθ + ε` — no error autocorrelation left.

    Lean: `GeoDa.sdemDes_iff_slxDes_of_lam_zero`. LeSage (2014): "SDEM subsumes SLX".
    """
    W, X, beta, theta, eps, _ = _instance(seed)
    u, y = sdem_reduced(W, 0.0, X, beta, theta, eps)
    assert np.allclose(u, eps, atol=TOL)
    assert np.allclose(y, X @ beta + (W @ X) @ theta + eps, atol=TOL)


@pytest.mark.parametrize("seed", range(4))
def test_sdem_with_theta_zero_is_sem(seed):
    """SDEM with `θ = 0` is SEM, and `spreg`'s SEM DGP agrees.

    Lean: `GeoDa.sdemDes_iff_semDes_of_theta_zero`. LeSage (2014): "SDEM subsumes SEM".
    """
    W, X, beta, _, eps, lam = _instance(seed)
    _, y = sdem_reduced(W, lam, X, beta, np.zeros_like(beta), eps)

    w = to_pysal_W(W)
    y_spreg = dgp_sperror(_col(eps), _col(X @ beta), w, lam=lam, imethod="true_inv")
    assert np.allclose(y_spreg.ravel(), y, atol=SPREG_TOL)

    u_sem, y_sem = sem_reduced(W, lam, X, beta, eps)
    assert np.allclose(y, y_sem, atol=TOL)


def test_the_two_nestings_compose_to_slx_only_when_both_coefficients_vanish():
    """Switching off `λ` alone leaves the `WXθ` term, and `θ` alone leaves the error term: the
    two nestings are independent, which is what makes SDEM the fourth corner of the square
    SLX / SEM / SDEM / (SDM, GNS)."""
    W, X, beta, theta, eps, _ = _instance(0)
    _, y_sdem = sdem_reduced(W, 0.4, X, beta, theta, eps)
    _, y_lambda0 = sdem_reduced(W, 0.0, X, beta, theta, eps)
    _, y_theta0 = sdem_reduced(W, 0.4, X, beta, np.zeros_like(beta), eps)
    assert not np.allclose(y_sdem, y_lambda0, atol=TOL)
    assert not np.allclose(y_sdem, y_theta0, atol=TOL)


# --------------------------------------------------------------------------------------
# Degenerate cases
# --------------------------------------------------------------------------------------


def test_the_reduced_form_is_singular_at_the_stability_boundary():
    """`|λ| < 1` is not slack: at `λ = 1` with a row-stochastic `W` the multiplier is
    singular and the reduced form does not exist.

    Lean: `GeoDa.isUnit_one_sub_smul_of_rowSubstochastic`, whose hypothesis is `|λ| < 1`.
    """
    with pytest.raises(np.linalg.LinAlgError):
        sdem_reduced(WSWAP, 1.0, X2, np.array([1.0]), np.array([1.0]), np.array([1.0, 1.0]))


def test_spreg_default_power_exp_fails_near_the_stability_boundary():
    """`spreg`'s default `imethod="power_exp"` is a truncated expansion, and near `|λ| = 1`
    it does not merely lose accuracy — it refuses.

    Two things are recorded here, both of which the Lean side explains. Inside the interior
    the series converges and the truncation error is small, which is
    `GeoDa.isUnit_one_sub_smul_of_rowSubstochastic` in numbers: `‖W *ᵥ v‖ ≤ ‖v‖` makes the
    terms shrink like `|λ|ᵏ`. Near the boundary the convergence criterion fails and `spreg`
    raises `"power expansion will not converge"` rather than returning a wrong number, which
    is the right behaviour and still a failure case worth knowing about.

    Every comparison above asks for `imethod="true_inv"` precisely so that none of this can
    be mistaken for a disagreement about the model.
    """
    W, X, beta, theta, eps, _ = _instance(0)
    w = to_pysal_W(W)

    y_series = dgp_slxerror(_col(eps), _col(X @ beta), _col((W @ X) @ theta), w,
                            lam=0.2, imethod="power_exp")
    _, y_exact = sdem_reduced(W, 0.2, X, beta, theta, eps)
    assert np.max(np.abs(y_series.ravel() - y_exact)) < 1e-9

    with pytest.raises(Exception, match="power expansion"):
        dgp_slxerror(_col(eps), _col(X @ beta), _col((W @ X) @ theta), w,
                     lam=0.99, imethod="power_exp")
