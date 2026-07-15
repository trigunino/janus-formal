"""Toy model where the inter-sector coupling is induced by metric mismatch."""

import numpy as np

from compare_models import evaluate


def metric_mismatch(c: float) -> float:
    """Absolute trace mismatch for diagonal 1+1D background metrics."""
    g_plus = np.diag([1.0, -1.0])
    g_minus = np.diag([1.0, -(c * c)])
    return abs(np.trace(np.linalg.inv(g_plus) @ g_minus) - 2.0)


def induced_coupling(c: float, alpha: float = 0.2) -> float:
    return alpha * metric_mismatch(c)


if __name__ == "__main__":
    print("c metric_mismatch coupling concurrence chsh_max")
    for c in (0.5, 0.8, 1.0, 1.2, 1.5):
        coupling = induced_coupling(c)
        result = evaluate(omega_minus=1.0, coupling=coupling)
        print(
            f"{c:3.1f} {metric_mismatch(c):15.6f} {coupling:8.6f} "
            f"{result['concurrence']:11.6f} {result['chsh_max']:8.6f}"
        )
