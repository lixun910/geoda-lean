"""Tests for the Monte Carlo benchmark harness.

These test the *harness*, not the estimators: that the support matrix is explicit,
that an unsupported model/estimator pair raises instead of silently substituting a
different estimator, that `betas` and the standard errors are aligned, that runs are
seeded and reproducible, and that the outputs are machine-readable.

They deliberately make no claim about estimator behaviour. Bias, RMSE and coverage
numbers are *data*, produced by `benchmark.py`; a passing test here says nothing about
whether an estimator is any good, and nothing at all about the Lean theorems.
"""

from __future__ import annotations

import csv
import json

import numpy as np
import pytest

from benchmark import benchmark as B

pytest.importorskip("spreg", reason="PySAL spreg is required for the benchmark")
pytest.importorskip("libpysal", reason="libpysal is required for the benchmark")


TINY = dict(n_side=4, reps=5)


def test_support_matrix_is_explicit_and_gns_has_no_estimator():
    """GNS with `θ ≠ 0` and `λ ≠ 0` has no `spreg` estimator, and the matrix says so.

    This is the one model in `GeoDa/` that `spreg` cannot fit, and the whole point of
    `SUPPORT` is that the harness says that out loud rather than fitting something
    close and calling it GNS.
    """
    assert B.SUPPORT["gns"] == ()
    assert "sarar" in B.SUPPORT, "SARAR is GNS with theta = 0 and does have an estimator"
    for model, ests in B.SUPPORT.items():
        for est in ests:
            assert est in B.ESTIMATORS, f"{model} -> {est} is not a known estimator"


def test_unsupported_combination_raises_and_never_substitutes():
    W, _ = B.lattice_weights(4, False)
    cell = B.Cell(model="gns", estimator="GM_Combo", rho=0.5, lam=0.5, **TINY)
    rng = np.random.default_rng(0)
    X, y = rng.normal(size=(cell.n, cell.k)), rng.normal(size=cell.n)
    with pytest.raises(ValueError) as info:
        B.fit(cell, X, y, W)
    assert "not supported" in str(info.value)
    assert "substitutes" in str(info.value)


def test_every_supported_pair_fits_and_the_layout_matches_betas():
    """`betas` and the parameter labels line up, for every supported pair.

    A mis-sliced `betas` still produces numbers -- they are just not the parameters
    you think they are -- so this is checked for every pair rather than assumed.
    """
    for model, ests in B.SUPPORT.items():
        for est in ests:
            cell = B.Cell(model=model, estimator=est, rho=0.5, lam=0.5, **TINY)
            w, W = B.lattice_weights(cell.n_side, cell.islands)
            rng = np.random.default_rng(1)
            X, y = B.make_design(cell, rng, W)
            betas, se = B.fit(cell, X, y, w)
            names = B.estimator_layout(est, cell.k, cell.k - 1 if model == "sdm" else 0)
            assert betas.shape == se.shape
            assert len(names) == betas.shape[0], (model, est, names, betas.shape)
            assert np.all(np.isfinite(betas)), (model, est)


def test_standard_errors_are_aligned_and_missing_ones_are_declared():
    """`spreg` reports one standard error fewer than `betas` for `GM_Combo` only.

    The missing one is `lambda`, which the estimator does not report. That is declared
    in `ESTIMATORS['GM_Combo'].no_se` and asserted in `fit`, so the errors cannot
    silently shift by one.
    """
    cell = B.Cell(model="sarar", estimator="GM_Combo", rho=0.5, lam=0.5, **TINY)
    w, W = B.lattice_weights(cell.n_side, cell.islands)
    rng = np.random.default_rng(2)
    X, y = B.make_design(cell, rng, W)
    betas, se = B.fit(cell, X, y, w)
    names = B.estimator_layout("GM_Combo", cell.k, 0)
    assert len(names) == betas.shape[0] == se.shape[0]
    assert np.isnan(se[names.index("lam")]), "lambda has no standard error here"
    assert np.all(np.isfinite(se[: names.index("lam")]))


def test_replications_are_seeded_and_reproducible():
    """The same config gives the same numbers: nothing depends on wall-clock time."""
    cell = B.Cell(model="sar", estimator="ML_Lag", rho=0.5, lam=0.0, **TINY)
    a = B.run_cell(cell)
    b = B.run_cell(cell)
    assert len(a.estimates) == len(b.estimates) == cell.reps
    assert np.allclose(np.asarray(a.estimates), np.asarray(b.estimates))
    assert a.seconds > 0.0


def test_smoke_benchmark_writes_machine_readable_outputs(tmp_path):
    """`write_results` produces parseable JSON per cell and one CSV summary."""
    cells = [
        B.Cell(model="sar", estimator="ML_Lag", rho=0.5, lam=0.0, **TINY),
        B.Cell(model="sem", estimator="ML_Error", rho=0.5, lam=0.5, **TINY),
    ]
    results = [B.run_cell(c) for c in cells]
    out = B.write_results("test", results, root=tmp_path)

    csv_path = out / "summary.csv"
    assert csv_path.exists()
    with csv_path.open() as fh:
        rows = list(csv.DictReader(fh))
    assert rows, "the CSV summary is empty"
    for row in rows:
        assert row["model"] in B.SUPPORT
        assert row["parameter"]
        assert row["failures"] == "0"
        float(row["true_value"])
        if row["bias"]:
            float(row["bias"])

    jsons = sorted(out.glob("*.json"))
    assert len(jsons) == len(cells)
    for path in jsons:
        d = json.loads(path.read_text())
        assert d["reps_requested"] == TINY["reps"]
        assert d["reps_used"] == TINY["reps"]
        assert d["failures"] == 0
        assert d["rows"], path
        assert d["cell"]["model"] in B.SUPPORT
        # The estimator's own description travels with the numbers.
        assert d["estimator"]["note"]


def test_islands_cell_is_actually_an_island():
    """The island variant really does have a zero row, in the `GeoDa.Island` sense."""
    w, W = B.lattice_weights(5, islands=True)
    assert np.allclose(W[0, :], 0.0), "region 0 should have no neighbours"
    assert np.allclose(W.sum(axis=1)[1:], 1.0), "every other row is row-standardized"


def test_sdm_cell_drops_the_lagged_intercept():
    """The SDM design lags only the non-constant regressors.

    Under row standardization `W·1 = 1`, so the lagged intercept is collinear with the
    intercept and only `β₀ + θ₀` is identified. The benchmark drops it explicitly and
    reports the intercept-free parameters; `Cell.truth` reflects that.
    """
    cell = B.Cell(model="sdm", estimator="ML_Lag_Durbin", rho=0.5, lam=0.0, k=3, **TINY)
    truth = cell.truth()
    assert "beta0" not in truth, "the intercept is not separately identified in SDM"
    assert "theta0" in truth and "rho" in truth
    assert len(B.estimator_layout("ML_Lag_Durbin", cell.k, cell.k - 1)) == 2 * cell.k
