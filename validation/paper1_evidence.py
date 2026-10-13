"""Reproduce Paper 1 SDEM absolute errors and the power-expansion guard failure.

Run from the repository root: python validation/paper1_evidence.py
Numerical observations only; no formal-verification claim.
"""
import hashlib
import inspect
import json
import platform

import numpy as np
import scipy
import spreg
from scipy.linalg import norm
from spreg.dgp import dgp_slxerror
from spreg.utils import power_expansion

from geoda_reference import sdem_reduced, to_pysal_W
from test_sdem import _col, _instance


def main():
    rows = []
    for islands, seeds in [(False, range(6)), (True, range(4))]:
        for seed in seeds:
            W, X, beta, theta, eps, lam = _instance(seed, islands=islands)
            w = to_pysal_W(W, row_standard=not islands)
            actual = dgp_slxerror(_col(eps), _col(X @ beta), _col((W @ X) @ theta),
                                  w, lam=lam, imethod="true_inv").ravel()
            _, expected = sdem_reduced(W, lam, X, beta, theta, eps)
            error = float(np.max(np.abs(actual - expected)))
            assert error <= 1e-8
            rows.append(dict(seed=seed, islands=islands, max_abs_error=error))
    W, X, beta, theta, eps, _ = _instance(0)
    increment = _col(eps)
    norms = []
    previous = 10000000.0
    first_increase = None
    for iteration in range(1, 101):
        increment = 0.99 * W @ increment
        norms.append(dict(iteration=iteration, norm2=float(norm(increment)),
                          norm_inf=float(np.max(np.abs(increment)))))
        if norm(increment) > previous:
            first_increase = dict(iteration=iteration, previous_norm2=previous,
                                  norm2=float(norm(increment)))
            break
        previous = float(norm(increment))
    try:
        dgp_slxerror(_col(eps), _col(X @ beta), _col((W @ X) @ theta),
                    to_pysal_W(W), lam=0.99, imethod="power_exp")
    except Exception as exc:
        guard_error = str(exc)
    else:
        guard_error = None
    assert guard_error is not None and 'power expansion' in guard_error
    print(json.dumps(dict(
        python=platform.python_version(), numpy=np.__version__, scipy=scipy.__version__,
        spreg=spreg.__version__, atol=1e-8, rtol=0.0, cases=rows,
        max_abs_error=max(r['max_abs_error'] for r in rows),
        lambda_099_increment_norms=norms, first_norm_increase=first_increase,
        guard_error=guard_error,
        spectral_radius=float(np.max(np.abs(np.linalg.eigvals(0.99 * W)))),
        power_expansion_source_sha256=hashlib.sha256(
            inspect.getsource(power_expansion).encode()).hexdigest()), indent=2))


if __name__ == '__main__':
    main()
