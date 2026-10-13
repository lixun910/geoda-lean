"""Numerical study of the heterogeneous-`ρ` model of `GeoDa/HeteroRho.lean`.

The model is `y = diag(ρ) W y + Xβ + ε`, so that each region has its own autoregressive
parameter. Lean proves two things about it, and these tests are the numerical counterpart:

* `GeoDa.isUnit_one_sub_diagMul_of_rowSubstochastic` — the system has exactly one solution
  when `W` is nonnegative row-substochastic and the parameters are uniformly bounded by
  `c < 1`;
* `GeoDa.heteroSAR_reducedForm_island_invariant` — and, in the other direction,
  `GeoDa.heteroSAR_parameter_identified`: `ρ i` is invisible exactly when row `i` of `W` is
  an island.

As everywhere in `validation/`, **none of this verifies anything.** The Lean theorems are
the proof; these are checks that an independent implementation agrees with what they say,
and a place to record what a prototype estimator does.

The prototype estimator below is **not a feasible estimator**, and that is the point of
recording it. It solves the structural equation for `ρ` using `ε`, which no implementation
can observe. It is exact when it exists and undefined at an island, which is precisely the
shape the identifiability result predicts — and it is *not* evidence that `ρ` can be
estimated from data. A feasible estimator is an open obligation; see
`docs/research-note-heterogeneous-rho.md`.
"""

import numpy as np
import pytest

from geoda_reference import row_standardize

TOL = 1e-10


# --------------------------------------------------------------------------------------
# The model, as `GeoDa.HeteroSARDes` writes it
# --------------------------------------------------------------------------------------


def hetero_multiplier(W, rho):
    """`1 - diag(ρ) W` — `GeoDa.diagMul` subtracted from the identity."""
    W = np.asarray(W, dtype=float)
    return np.eye(W.shape[0]) - np.diag(np.asarray(rho, dtype=float)) @ W


def hetero_reduced(W, rho, X, beta, eps):
    """The reduced form `(1 - diag(ρ)W)⁻¹ (Xβ + ε)` — `GeoDa.heteroSARDes_iff_reducedForm`."""
    z = np.asarray(X, dtype=float) @ np.asarray(beta, dtype=float) + np.asarray(eps, dtype=float)
    return np.linalg.solve(hetero_multiplier(W, rho), z)


def proto_estimator(W, y, z):
    """**Prototype, and not a feasible estimator.** Recover `ρ` from the structural
    equation `y - z = diag(ρ) W y`, coordinatewise:

        ρ i = (y i - z i) / (W y) i

    It is exact whenever the denominator is nonzero, and undefined — `nan`, not a number —
    where it is zero. It needs `z = Xβ + ε`, in particular `ε`, which no real estimator
    observes; it exists here only to make the identifiability result visible.

    Returns `(rho_hat, defined)` where `defined` marks the coordinates that could be
    recovered at all.
    """
    Wy = np.asarray(W, dtype=float) @ np.asarray(y, dtype=float)
    num = np.asarray(y, dtype=float) - np.asarray(z, dtype=float)
    defined = Wy != 0.0
    rho_hat = np.full(num.shape, np.nan)
    rho_hat[defined] = num[defined] / Wy[defined]
    return rho_hat, defined


def island_weights():
    """Row `0` all zeros: region `0` has no neighbours. `GeoDaTest.Wisland`."""
    return np.array([[0.0, 0.0], [1.0, 0.0]])


def cycle_weights():
    """No zero row: `GeoDaTest.Wswap`."""
    return np.array([[0.0, 1.0], [1.0, 0.0]])


# --------------------------------------------------------------------------------------
# Non-identification at an island
# --------------------------------------------------------------------------------------


@pytest.mark.parametrize("seed", range(4))
def test_island_parameter_is_exactly_invisible(seed):
    """Two different `ρ` differing only at an island produce **bit-identical** data.

    Not "close": identical. `ρ 0` multiplies a zero row, so it does not enter the model at
    all — `GeoDa.diagMul_update_island`, and hence
    `GeoDa.heteroSAR_reducedForm_island_invariant`, in numbers.

    This is the strongest form the check can take, and it is why the identifiability
    statement is worth having: no estimator, however good, can separate these two
    parameter vectors.
    """
    rng = np.random.default_rng(seed)
    W = island_weights()
    X = np.hstack([np.ones((2, 1)), rng.normal(size=(2, 1))])
    beta, eps = rng.normal(size=2), rng.normal(size=2)

    rho_a = np.array([0.25, 0.5])
    rho_b = np.array([0.75, 0.5])  # differs only at the island

    M_a, M_b = hetero_multiplier(W, rho_a), hetero_multiplier(W, rho_b)
    assert np.array_equal(M_a, M_b), "the multipliers should agree exactly"

    y_a = hetero_reduced(W, rho_a, X, beta, eps)
    y_b = hetero_reduced(W, rho_b, X, beta, eps)
    assert np.array_equal(y_a, y_b), "so the data are identical, bit for bit"


@pytest.mark.parametrize("seed", range(4))
def test_no_island_parameter_is_visible(seed):
    """Away from islands, changing `ρ` does change the data — the other direction.

    `GeoDa.diagMul_injective_of_no_island`.
    """
    rng = np.random.default_rng(seed)
    W = cycle_weights()
    X = np.hstack([np.ones((2, 1)), rng.normal(size=(2, 1))])
    beta, eps = rng.normal(size=2), rng.normal(size=2)

    y_a = hetero_reduced(W, np.array([0.25, 0.5]), X, beta, eps)
    y_b = hetero_reduced(W, np.array([0.75, 0.5]), X, beta, eps)
    assert not np.allclose(y_a, y_b, atol=TOL)


# --------------------------------------------------------------------------------------
# The prototype estimator: exact where defined, undefined at an island
# --------------------------------------------------------------------------------------


@pytest.mark.parametrize("seed", range(6))
def test_prototype_recovers_rho_when_no_row_is_an_island(seed):
    """Where the model is identified, the prototype recovers `ρ` to round-off.

    Read this as a check that `GeoDa.heteroSARDes_iff_reducedForm` and the structural
    equation say the same thing, *not* as a bias/RMSE result for an estimator: the
    prototype sees `ε`.
    """
    rng = np.random.default_rng(seed)
    W = cycle_weights()
    rho = rng.uniform(-0.8, 0.8, size=2)
    X = np.hstack([np.ones((2, 1)), rng.normal(size=(2, 1))])
    beta, eps = rng.normal(size=2), rng.normal(size=2)
    z = X @ beta + eps

    y = hetero_reduced(W, rho, X, beta, eps)
    rho_hat, defined = proto_estimator(W, y, z)

    assert defined.all(), "no island, so every coordinate should be recoverable"
    assert np.allclose(rho_hat, rho, atol=1e-9), (rho_hat, rho)


def test_prototype_is_undefined_at_the_island():
    """At an island the prototype has nothing to divide by, and says so.

    `W y` is zero in row `0` because row `0` of `W` is zero, and `y 0 = z 0` always. The
    ratio is `0 / 0`; the honest answer is "not identified", not a number.
    """
    rng = np.random.default_rng(0)
    W = island_weights()
    X = np.hstack([np.ones((2, 1)), rng.normal(size=(2, 1))])
    beta, eps = rng.normal(size=2), rng.normal(size=2)
    z = X @ beta + eps

    y = hetero_reduced(W, np.array([0.25, 0.5]), X, beta, eps)
    rho_hat, defined = proto_estimator(W, y, z)

    assert not defined[0], "the island's coordinate is not recoverable"
    assert np.isnan(rho_hat[0])
    assert defined[1] and np.isclose(rho_hat[1], 0.5, atol=1e-9)

    # And the failure is not numerical noise: the data are the same whatever ρ 0 is.
    y_other = hetero_reduced(W, np.array([-0.9, 0.5]), X, beta, eps)
    assert np.array_equal(y, y_other)


# --------------------------------------------------------------------------------------
# The uniform bound
# --------------------------------------------------------------------------------------


def test_uniform_bound_is_not_slack():
    """The hypothesis of `isUnit_one_sub_diagMul_of_rowSubstochastic` is a *uniform* bound
    `c < 1`, and `c` cannot be replaced by `1`.

    `GeoDa.Multiplier` proves that for a scalar `ρ`. Here, with one parameter per region,
    the same failure appears coordinatewise: a nonnegative row-stochastic `W` at `c = 1`
    gives a singular multiplier. The Lean theorem's `c < 1` is what rules it out.
    """
    W = cycle_weights()  # row-stochastic
    M = hetero_multiplier(W, np.ones(2))  # c = 1
    assert np.linalg.matrix_rank(M) < 2, "1 - diag(1) W should be singular"
    with pytest.raises(np.linalg.LinAlgError):
        np.linalg.solve(M, np.ones(2))

    # The same `W` with parameters inside the interior is fine.
    assert np.linalg.matrix_rank(hetero_multiplier(W, np.full(2, 0.99))) == 2


def test_contraction_estimate_holds_with_a_uniform_bound():
    """`‖diag(ρ) W v‖∞ ≤ c ‖v‖∞` — `GeoDa.norm_mulVec_diagMul_le` — checked directly."""
    rng = np.random.default_rng(3)
    n = 6
    A = (rng.random((n, n)) < 0.5).astype(float)
    np.fill_diagonal(A, 0.0)
    A[A.sum(axis=1) == 0.0, 1] = 1.0
    W = row_standardize(A)

    for c in (0.2, 0.5, 0.8):
        rho = rng.uniform(-c, c, size=n)
        M = np.diag(rho) @ W
        for _ in range(20):
            v = rng.normal(size=n)
            assert np.max(np.abs(M @ v)) <= c * np.max(np.abs(v)) + 1e-12
