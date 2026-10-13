"""Reference implementations of the GeoDa-Lean spatial model formulas.

Each function mirrors a definition in the Lean sources:

* ``GeoDa/Weights.lean``     -- ``SARMat``, ``SEMMat``, ``SDMMat``, ``GNSMat``
* ``GeoDa/Design.lean``      -- ``Xβ = X *ᵥ β``, ``WXθ = (W * X) *ᵥ θ``
* ``GeoDa/SpatialWeights.lean`` -- predicates and ``normalize``
* ``GeoDa/ReducedForm.lean`` -- ``u = B⁻¹ε``, ``y = A⁻¹(Xβ + WXθ + B⁻¹ε)``,
  with ``A = I - ρW`` and ``B = I - λW``

They are written with ``numpy.linalg.solve`` rather than with an explicit matrix
inverse, so that they are computed independently of both Lean and PySAL.

**Nothing in this directory is verified.** Lean *verifies* the identities -- see
``GeoDa.gnsDes_iff_reducedForm`` and the audit in ``GeoDaTest/Axioms.lean``. These
functions and the tests that use them only offer a second, independent computation
of a concrete instance. Agreement is evidence about the two implementations, and is
not a substitute for ``./scripts/verify.sh``.
"""

from __future__ import annotations

import numpy as np

__all__ = [
    "spatial_multiplier",
    "gns_reduced",
    "sar_reduced",
    "sem_reduced",
    "sdm_reduced",
    "structural_residuals",
    "row_standardize",
    "to_pysal_W",
]


def spatial_multiplier(W: np.ndarray, coeff: float) -> np.ndarray:
    """``A = I - coeff * W``, the Lean ``1 - ρ • W``."""
    W = np.asarray(W, dtype=float)
    return np.eye(W.shape[0]) - coeff * W


def _xb_wxg(W, X, beta, theta, n):
    """``Xβ`` and ``WXθ``, exactly as ``GeoDa.Design`` forms them."""
    X = np.asarray(X, dtype=float).reshape(n, -1)
    xb = X @ np.asarray(beta, dtype=float)
    # WXθ = (W * X) *ᵥ θ  -- GeoDa.Design.wxθ / design_wxθ_eq
    wxg = (np.asarray(W, dtype=float) @ X) @ np.asarray(theta, dtype=float)
    return xb, wxg


def gns_reduced(W, rho, lam, X, beta, theta, eps):
    """Full GNS reduced form. Returns ``(u, y)``.

    Lean: ``GeoDa.gnsDes_iff_reducedForm`` --
    ``u = B⁻¹ε`` and ``y = A⁻¹(Xβ + WXθ + B⁻¹ε)`` with ``A = I - ρW``,
    ``B = I - λW``.
    """
    eps = np.asarray(eps, dtype=float).ravel()
    n = eps.shape[0]
    A = spatial_multiplier(W, rho)
    B = spatial_multiplier(W, lam)
    u = np.linalg.solve(B, eps)
    xb, wxg = _xb_wxg(W, X, beta, theta, n)
    y = np.linalg.solve(A, xb + wxg + u)
    return u, y


def sar_reduced(W, rho, X, beta, eps):
    """SAR reduced form ``y = A⁻¹(Xβ + ε)``. Lean: ``GeoDa.sarMat_iff_reducedForm``."""
    eps = np.asarray(eps, dtype=float).ravel()
    xb = np.asarray(X, dtype=float).reshape(eps.shape[0], -1) @ np.asarray(beta, dtype=float)
    return np.linalg.solve(spatial_multiplier(W, rho), xb + eps)


def sem_reduced(W, lam, X, beta, eps):
    """SEM reduced form ``u = B⁻¹ε``, ``y = Xβ + u``.

    Lean: ``GeoDa.semMat_iff_reducedForm``.
    """
    eps = np.asarray(eps, dtype=float).ravel()
    xb = np.asarray(X, dtype=float).reshape(eps.shape[0], -1) @ np.asarray(beta, dtype=float)
    u = np.linalg.solve(spatial_multiplier(W, lam), eps)
    return u, xb + u


def sdm_reduced(W, rho, X, beta, theta, eps):
    """SDM reduced form ``y = A⁻¹(Xβ + WXθ + ε)``.

    Lean: ``GeoDa.sdmDes_iff_reducedForm`` -- the ``λ = 0`` restriction of GNS,
    where ``B = I`` and ``u = ε``.
    """
    u, y = gns_reduced(W, rho, 0.0, X, beta, theta, eps)
    return y


def structural_residuals(W, rho, lam, X, beta, theta, eps, u, y):
    """Residuals of the two *structural* GNS equations for a given ``(u, y)``.

    Both are zero exactly when ``(u, y)`` solves the structural system

        ``y = ρWy + Xβ + WXθ + u``   and   ``u = λWu + ε``,

    which is what ``GeoDa.GNSDes`` asserts. The reduced form is only legitimate
    because the converse holds too -- ``GeoDa.gnsDes_iff_reducedForm``.
    """
    W = np.asarray(W, dtype=float)
    eps = np.asarray(eps, dtype=float).ravel()
    u = np.asarray(u, dtype=float).ravel()
    y = np.asarray(y, dtype=float).ravel()
    xb, wxg = _xb_wxg(W, X, beta, theta, eps.shape[0])
    return y - (rho * (W @ y) + xb + wxg + u), u - (lam * (W @ u) + eps)


def row_standardize(W: np.ndarray) -> np.ndarray:
    """Row standardization with the island convention of ``GeoDa.normalize``.

    Each row is divided by its sum. A **zero row stays a zero row**: there is no
    division by zero, matching ``(0 : ℝ)⁻¹ = 0`` in ``GeoDa/SpatialWeights.lean``
    and ``GeoDa.island_normalize``.
    """
    W = np.asarray(W, dtype=float)
    s = W.sum(axis=1, keepdims=True)
    out = np.zeros_like(W)
    nz = s[:, 0] != 0.0
    out[nz] = W[nz] / s[nz]
    return out


def to_pysal_W(W: np.ndarray, row_standard: bool = True):
    """Build a ``libpysal`` weights object from a dense matrix.

    A zero entry means "no link", so a row that is entirely zero is an *island*:
    it has no neighbours, and ``transform = "r"`` leaves it zero. This is the same
    convention as ``GeoDa.Island`` and ``GeoDa.normalize``.
    """
    import libpysal

    W = np.asarray(W, dtype=float)
    n = W.shape[0]
    neighbors, weights = {}, {}
    for i in range(n):
        js = [j for j in range(n) if W[i, j] != 0.0]
        neighbors[i] = js
        weights[i] = [float(W[i, j]) for j in js]
    w = libpysal.weights.W(neighbors, weights, silence_warnings=True)
    w.transform = "r" if row_standard else "o"
    return w
