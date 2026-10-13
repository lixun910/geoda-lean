"""Monte Carlo benchmark for PySAL `spreg` estimators of the GeoDa-Lean models.

What this measures, and what it does not
----------------------------------------

This is an **empirical** study of *estimators*. It samples data from the exact
data-generating processes that `GeoDa/` formalizes, fits `spreg` estimators, and
reports how often and how far the estimates miss the parameters that were used to
generate the data.

It is not a proof, and it cannot be one. `GeoDa/` proves statements about *model
equations* -- identities, equivalences, invertibility -- and says nothing about
estimators, consistency or asymptotic distributions. Nothing in `results/` supports
or undermines any Lean theorem. Only `./scripts/verify.sh` verifies anything.

What it *is* good for is the opposite direction: it checks that the equations this
repository writes down are the equations an implementation fits, and it shows where
an estimator's behaviour stops being trustworthy -- near the stability bound, and in
the presence of islands.

Determinism
-----------

Every replication derives its generator from ``default_rng(seed_base + rep)`` with a
documented, fixed ``seed_base`` per cell, so a run is reproducible from the config
alone. Nothing depends on wall-clock time or on iteration order.

Usage
-----

    python validation/benchmark/benchmark.py --smoke      # CI scale -> results/smoke/
    python validation/benchmark/benchmark.py --extended   # opt-in  -> results/extended/
    python validation/benchmark/benchmark.py --list       # the support matrix
"""

from __future__ import annotations

import argparse
import csv
import json
import sys
import time
import warnings
from dataclasses import dataclass, field
from pathlib import Path

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from geoda_reference import gns_reduced, row_standardize, to_pysal_W  # noqa: E402

import libpysal  # noqa: E402
import spreg  # noqa: E402

# `spreg`'s ML estimators call `scipy.optimize.minimize_scalar` with a relative
# tolerance it cannot honour for the 'bounded' method; the warning is benign and
# would otherwise drown the run.
warnings.filterwarnings("ignore", message="Method 'bounded' does not support")

RESULTS_ROOT = Path(__file__).resolve().parent / "results"
Z95 = 1.959963984540054


# ======================================================================================
# The support matrix
# ======================================================================================


@dataclass(frozen=True)
class Estimator:
    """One `spreg` estimator, and where its parameters sit in ``betas``.

    ``layout`` names every entry of ``betas`` in order. This is stated explicitly
    because getting it wrong is silent: a mis-sliced ``betas`` still produces numbers,
    they are just not the parameters you think they are.
    """

    name: str
    callable: str
    layout: tuple[str, ...]  # 'beta', 'theta', 'rho', 'lam' per entry
    note: str
    #: layout slots for which `spreg` reports *no* standard error. Getting this wrong
    #: would silently misalign `std_err` against `betas`, so it is declared rather than
    #: guessed, and `fit` asserts against it.
    no_se: tuple[str, ...] = ()


#: Which estimators fit which model. **There is no silent substitution anywhere**: a
#: combination missing from this table raises, it does not fall back to something else.
#:
#: `gns` here means *our* GNS, `y = ρWy + Xβ + WXθ + u`, `u = λWu + ε`, with `θ ≠ 0`
#: *and* `λ ≠ 0`. `spreg` has no such estimator; `GM_Combo` fits SARAR, which is the
#: `θ = 0` case. That is why `gns` maps to the empty tuple.
SUPPORT: dict[str, tuple[str, ...]] = {
    "sar": ("ML_Lag", "GM_Lag"),
    "sem": ("ML_Error", "GM_Error_Hom"),
    "sdm": ("ML_Lag_Durbin",),
    "sarar": ("GM_Combo",),
    "gns": (),
}

ESTIMATORS: dict[str, Estimator] = {
    "ML_Lag": Estimator(
        "ML_Lag", "spreg.ML_Lag", ("beta", "rho"),
        "maximum likelihood for y = ρWy + Xβ + ε",
    ),
    "GM_Lag": Estimator(
        "GM_Lag", "spreg.GM_Lag", ("beta", "rho"),
        "GM/2SLS for the same model; no distributional assumption, robust to "
        "non-normality, less efficient than ML",
    ),
    "ML_Lag_Durbin": Estimator(
        "ML_Lag_Durbin", "spreg.ML_Lag",
        ("beta", "theta", "rho"),
        "ML_Lag applied to [X, WX̃]; this is SDM, not a substitute for it. X̃ excludes "
        "any constant column, because W·1 = 1 under row standardization makes the "
        "lagged intercept collinear with the intercept: only β_0 + θ_0 is identified",
    ),
    "ML_Error": Estimator(
        "ML_Error", "spreg.ML_Error", ("beta", "lam"),
        "maximum likelihood for y = Xβ + u, u = λWu + ε",
    ),
    "GM_Error_Hom": Estimator(
        "GM_Error_Hom", "spreg.GM_Error_Hom", ("beta", "lam"),
        "GM for the same model, assuming homoskedasticity",
    ),
    "GM_Combo": Estimator(
        "GM_Combo", "spreg.GM_Combo", ("beta", "rho", "lam"),
        "GM for SARAR, i.e. GNS with θ = 0. Note: spreg reports no standard error for "
        "lambda here, so no coverage is claimed for it",
        no_se=("lam",),
    ),
}


def estimator_layout(name: str, k_beta: int, k_theta: int) -> list[str]:
    """Expand an estimator's ``layout`` into one label per ``betas`` entry."""
    out: list[str] = []
    for part in ESTIMATORS[name].layout:
        if part == "beta":
            out += [f"beta{i}" for i in range(k_beta)]
        elif part == "theta":
            out += [f"theta{i}" for i in range(k_theta)]
        else:
            out.append(part)
    return out


# ======================================================================================
# Weights
# ======================================================================================


def lattice_weights(n_side: int, islands: bool) -> tuple[object, np.ndarray]:
    """Row-standardized rook contiguity on an ``n_side × n_side`` lattice.

    With ``islands=True``, region 0's links are removed before standardizing, so its
    row is entirely zero. That is an *island* in the sense of `GeoDa.Island`, and the
    re-standardization leaves it zero rather than dividing by zero -- the same
    convention as `GeoDa.normalize`.
    """
    w = libpysal.weights.lat2W(n_side, n_side)
    w.transform = "r"
    dense = w.full()[0]
    if islands:
        dense = dense.copy()
        dense[0, :] = 0.0
        dense[:, 0] = 0.0
        dense = row_standardize(dense)
        w = to_pysal_W(dense, row_standard=False)
    return w, dense


# ======================================================================================
# The data-generating processes -- exactly the equations GeoDa/ formalizes
# ======================================================================================


@dataclass
class Cell:
    """One Monte Carlo cell: a model, a design, and the parameters to recover."""

    model: str
    estimator: str
    n_side: int
    rho: float
    lam: float
    islands: bool = False
    k: int = 3
    beta: tuple[float, ...] = (1.0, 1.0, -0.5)
    theta: float = 0.6
    reps: int = 20
    seed_base: int = 20261013

    @property
    def n(self) -> int:
        return self.n_side * self.n_side

    @property
    def label(self) -> str:
        return (
            f"{self.model}-{self.estimator}-n{self.n}"
            f"{'-islands' if self.islands else ''}"
            f"-rho{self.rho}-lam{self.lam}"
        )

    def truth(self) -> dict[str, float]:
        """The parameters the estimator is supposed to recover.

        For SDM only ``beta`` excluding the intercept, ``theta`` and ``rho`` are
        reported: the intercept and the lagged intercept are not separately identified
        under row standardization (see `ESTIMATORS['ML_Lag_Durbin']`).
        """
        t = {f"beta{i}": v for i, v in enumerate(self.beta)}
        if self.model == "sdm":
            t.pop("beta0")  # identified only as beta0 + theta0
            t["theta0"] = self.theta
            t["rho"] = self.rho
        elif self.model == "sar":
            t["rho"] = self.rho
        elif self.model == "sem":
            t["lam"] = self.lam
        elif self.model == "sarar":
            t["rho"] = self.rho
            t["lam"] = self.lam
        return t


def make_design(cell: Cell, rng: np.random.Generator, W: np.ndarray):
    """``(X, y)`` sampled from the model in ``cell``.

    Each branch is a transcription of the equation `GeoDa/` formalizes, evaluated
    through `geoda_reference` so that the DGP and the Lean statements stay in step.
    """
    n = cell.n
    X = np.hstack(
        [np.ones((n, 1))] + [rng.normal(size=(n, 1)) for _ in range(cell.k - 1)]
    )
    beta = np.asarray(cell.beta, dtype=float)
    eps = rng.normal(size=n)

    if cell.model == "sar":
        _, y = gns_reduced(W, cell.rho, 0.0, X, beta, np.zeros(cell.k), eps)
    elif cell.model == "sem":
        _, y = gns_reduced(W, 0.0, cell.lam, X, beta, np.zeros(cell.k), eps)
    elif cell.model == "sdm":
        theta = np.zeros(cell.k)
        theta[1] = cell.theta  # lag only the non-constant regressors
        _, y = gns_reduced(W, cell.rho, 0.0, X, beta, theta, eps)
    elif cell.model == "sarar":
        _, y = gns_reduced(W, cell.rho, cell.lam, X, beta, np.zeros(cell.k), eps)
    else:  # pragma: no cover - guarded by SUPPORT
        raise ValueError(f"no DGP for model {cell.model!r}")
    return X, y


# ======================================================================================
# Estimation
# ======================================================================================


def fit(cell: Cell, X: np.ndarray, y: np.ndarray, w):
    """Fit the cell's estimator. Raises if the combination is unsupported."""
    if cell.estimator not in SUPPORT[cell.model]:
        raise ValueError(
            f"{cell.estimator!r} is not supported for model {cell.model!r}. "
            f"Supported: {SUPPORT[cell.model] or 'none -- spreg has no estimator for this model'}. "
            "This benchmark never substitutes a different estimator."
        )

    Y = y.reshape(-1, 1)
    if cell.estimator == "ML_Lag":
        res = spreg.ML_Lag(Y, X, w)
    elif cell.estimator == "GM_Lag":
        res = spreg.GM_Lag(Y, X, w=w)
    elif cell.estimator == "ML_Lag_Durbin":
        # SDM: regressors are [X, WX̃], where X̃ drops the constant column, because
        # W·1 = 1 makes the lagged intercept collinear with the intercept.
        Xt = X[:, 1:]
        res = spreg.ML_Lag(Y, np.hstack([X, np.asarray(w.full()[0]) @ Xt]), w)
    elif cell.estimator == "ML_Error":
        res = spreg.ML_Error(Y, X, w)
    elif cell.estimator == "GM_Error_Hom":
        res = spreg.GM_Error_Hom(Y, X, w)
    elif cell.estimator == "GM_Combo":
        res = spreg.GM_Combo(Y, X, w=w)
    else:  # pragma: no cover
        raise ValueError(cell.estimator)

    betas = np.asarray(res.betas, dtype=float).ravel()
    raw_se = np.asarray(getattr(res, "std_err", []), dtype=float).ravel()
    n_missing = betas.shape[0] - raw_se.shape[0]
    expected = len(ESTIMATORS[cell.estimator].no_se)
    # Explicit, not heuristic: if `spreg` ever changes how many standard errors it
    # reports, this fires instead of silently pairing the wrong error with a parameter.
    assert n_missing == expected, (
        f"{cell.estimator}: betas has {betas.shape[0]} entries but std_err has "
        f"{raw_se.shape[0]}; expected exactly {expected} missing "
        f"({ESTIMATORS[cell.estimator].no_se}). Refusing to guess the alignment."
    )
    se = np.concatenate([raw_se, np.full(n_missing, np.nan)])
    return betas, se


# ======================================================================================
# The experiment
# ======================================================================================


@dataclass
class CellResult:
    cell: Cell
    names: list[str]
    estimates: list[list[float]] = field(default_factory=list)
    std_errors: list[list[float]] = field(default_factory=list)
    failures: int = 0
    seconds: float = 0.0

    def summary(self) -> list[dict]:
        """Bias, RMSE and 95% CI coverage per parameter, plus the failure count.

        Replications that raised, or that produced a non-finite estimate, are counted
        in ``failures`` and left out of the moments. They are *never* silently
        replaced by a different estimator's output; the count is reported alongside.
        """
        truth = self.cell.truth()
        est = np.asarray(self.estimates, dtype=float)
        se = np.asarray(self.std_errors, dtype=float)
        rows = []
        for j, name in enumerate(self.names):
            if name not in truth:
                continue
            if est.size == 0:
                rows.append(dict(parameter=name, true_value=truth[name], n_used=0,
                                 bias=None, rmse=None, coverage=None))
                continue
            e = est[:, j]
            s = se[:, j]
            bias = float(np.mean(e - truth[name]))
            rmse = float(np.sqrt(np.mean((e - truth[name]) ** 2)))
            if np.all(np.isnan(s)):  # the estimator reports no standard error here
                rows.append(dict(
                    parameter=name, true_value=float(truth[name]),
                    n_used=int(e.shape[0]), bias=bias, rmse=rmse,
                    coverage=None, mean_std_err=None, se_reported=False,
                    note="spreg reports no standard error for this parameter",
                ))
                continue
            covered = np.abs(e - truth[name]) <= Z95 * s
            rows.append(dict(
                parameter=name,
                true_value=float(truth[name]),
                n_used=int(e.shape[0]),
                bias=bias,
                rmse=rmse,
                coverage=float(np.mean(covered)),
                mean_std_err=float(np.mean(s)),
                se_reported=True,
            ))
        return rows

    def to_json(self) -> dict:
        return dict(
            cell=cell_to_dict(self.cell),
            label=self.cell.label,
            estimator=ESTIMATORS[self.cell.estimator].__dict__,
            names=self.names,
            reps_requested=self.cell.reps,
            reps_used=len(self.estimates),
            failures=self.failures,
            seconds=self.seconds,
            rows=self.summary(),
        )


def cell_to_dict(cell: Cell) -> dict:
    d = dict(cell.__dict__)
    d["beta"] = list(cell.beta)
    d["n"] = cell.n
    return d


def run_cell(cell: Cell, verbose: bool = False) -> CellResult:
    w, W = lattice_weights(cell.n_side, cell.islands)
    names = estimator_layout(cell.estimator, cell.k, cell.k - 1 if cell.model == "sdm" else 0)
    res = CellResult(cell=cell, names=names)
    t0 = time.perf_counter()
    for rep in range(cell.reps):
        rng = np.random.default_rng(cell.seed_base + rep)
        X, y = make_design(cell, rng, W)
        try:
            betas, se = fit(cell, X, y, w)
            if betas.shape[0] != len(names) or not np.all(np.isfinite(betas)):
                res.failures += 1
                continue
            res.estimates.append(betas.tolist())
            res.std_errors.append(se.tolist())
        except Exception:
            # A failure is data, not something to paper over.
            res.failures += 1
    res.seconds = time.perf_counter() - t0
    if verbose:
        print(f"    {cell.label}: {len(res.estimates)}/{cell.reps} ok, "
              f"{res.failures} failed, {res.seconds:.1f}s")
    return res


# ======================================================================================
# Configurations
# ======================================================================================


def smoke_cells() -> list[Cell]:
    """CI scale. Kept small enough to run on every push."""
    cells = []
    for model, est in (("sar", "ML_Lag"), ("sem", "ML_Error"), ("sarar", "GM_Combo")):
        for rho in (0.5, 0.8):
            cells.append(Cell(model=model, estimator=est, n_side=7, islands=False,
                              rho=rho, lam=rho, reps=50))
    cells.append(Cell(model="sdm", estimator="ML_Lag_Durbin", n_side=7, islands=False,
                      rho=0.5, lam=0.0, reps=50))
    # Islands: the degenerate structure `GeoDa.Island` allows.
    cells.append(Cell(model="sar", estimator="ML_Lag", n_side=7, islands=True,
                      rho=0.5, lam=0.0, reps=50))
    return cells


def extended_cells() -> list[Cell]:
    """The opt-in experiment. Not run in CI."""
    cells = []
    for model, ests in (
        ("sar", ("ML_Lag", "GM_Lag")),
        ("sem", ("ML_Error", "GM_Error_Hom")),
        ("sarar", ("GM_Combo",)),
        ("sdm", ("ML_Lag_Durbin",)),
    ):
        for est in ests:
            for n_side in (5, 10, 20):
                for islands in (False, True):
                    for rho in (0.2, 0.5, 0.8, 0.95):
                        for lam in (rho, 0.2):
                            if model in ("sar", "sdm") and lam != rho:
                                continue  # lam is unused by these DGPs
                            cells.append(Cell(model=model, estimator=est, n_side=n_side,
                                              islands=islands, rho=rho, lam=lam,
                                              reps=250, seed_base=771000 + 7 * n_side))
    return cells


# ======================================================================================
# Driver
# ======================================================================================


def write_results(tag: str, results: list[CellResult], root: Path = RESULTS_ROOT) -> Path:
    out = root / tag
    out.mkdir(parents=True, exist_ok=True)
    for res in results:
        (out / f"{res.cell.label}.json").write_text(
            json.dumps(res.to_json(), indent=2, sort_keys=True) + "\n"
        )
    with (out / "summary.csv").open("w", newline="") as fh:
        wr = csv.writer(fh)
        wr.writerow(["model", "estimator", "n", "islands", "rho", "lam", "label",
                     "reps_used", "failures", "seconds",
                     "parameter", "true_value", "n_used", "bias", "rmse", "coverage",
                     "mean_std_err", "se_reported", "note"])
        for res in results:
            c = res.cell
            for row in res.summary():
                wr.writerow([c.model, c.estimator, c.n, c.islands, c.rho, c.lam,
                             c.label, len(res.estimates), res.failures,
                             f"{res.seconds:.3f}", row["parameter"],
                             row["true_value"], row["n_used"],
                             row.get("bias"), row.get("rmse"), row.get("coverage"),
                             row.get("mean_std_err"), row.get("se_reported"),
                             row.get("note", "")])
    return out


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    g = ap.add_mutually_exclusive_group(required=True)
    g.add_argument("--smoke", action="store_true", help="CI-scale run")
    g.add_argument("--extended", action="store_true", help="opt-in full run")
    g.add_argument("--list", action="store_true", help="print the support matrix")
    args = ap.parse_args(argv)

    if args.list:
        print("model -> estimators supported by spreg\n")
        for model, ests in SUPPORT.items():
            print(f"  {model:6s} -> {', '.join(ests) if ests else '(none)'}")
            if not ests:
                print("           spreg has no estimator for GNS with theta != 0 "
                      "and lam != 0.")
        return 0

    cells = smoke_cells() if args.smoke else extended_cells()
    tag = "smoke" if args.smoke else "extended"
    print(f"running {len(cells)} cells ({tag})")
    results = []
    t0 = time.perf_counter()
    for cell in cells:
        results.append(run_cell(cell, verbose=True))
    out = write_results(tag, results)
    total = time.perf_counter() - t0
    print(f"wrote {out} ({total:.1f}s total)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
