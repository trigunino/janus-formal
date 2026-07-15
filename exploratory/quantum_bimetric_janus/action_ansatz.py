"""Action-inspired metric coupling ansatz.

This is a sandbox parametrisation, not a covariant Janus action.
"""

from metric_coupled_model import metric_mismatch
from compare_models import evaluate


def mismatch_signed(c: float) -> float:
    # For the chosen backgrounds: Tr(g_plus^-1 g_minus) - 2 = c^2 - 1.
    return c * c - 1.0


def potential(c: float, beta: float = 0.1) -> float:
    delta = mismatch_signed(c)
    return 0.5 * beta * delta * delta


def induced_coupling_from_action(c: float, beta: float = 0.1) -> float:
    # dU/dc for U = beta/2 (c^2 - 1)^2.
    return 2.0 * beta * c * mismatch_signed(c)


if __name__ == "__main__":
    print("c potential coupling concurrence chsh_max")
    for c in (0.5, 0.8, 1.0, 1.2, 1.5):
        coupling = induced_coupling_from_action(c)
        result = evaluate(omega_minus=1.0, coupling=coupling)
        print(
            f"{c:3.1f} {potential(c):9.6f} {coupling:8.6f} "
            f"{result['concurrence']:11.6f} {result['chsh_max']:8.6f}"
        )
