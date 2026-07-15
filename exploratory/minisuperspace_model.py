"""Minisuperspace reduction with two scale factors."""

from compare_models import evaluate


def interaction_potential(r: float, beta: float = 0.1) -> float:
    """Symmetric mismatch potential around equal scale factors."""
    return 0.5 * beta * (r - 1.0 / r) ** 2


def induced_coupling(r: float, alpha: float = 0.2) -> float:
    """Derivative-inspired coupling from the scale-factor ratio."""
    return alpha * (r - 1.0 / (r**3))


if __name__ == "__main__":
    print("a_plus a_minus ratio potential coupling concurrence chsh_max")
    for a_plus, a_minus in ((1.0, 1.0), (1.0, 1.2), (1.0, 1.5), (1.5, 1.0)):
        ratio = a_minus / a_plus
        coupling = induced_coupling(ratio)
        result = evaluate(omega_minus=1.0, coupling=coupling)
        print(
            f"{a_plus:6.2f} {a_minus:7.2f} {ratio:5.2f} "
            f"{interaction_potential(ratio):9.6f} {coupling:8.6f} "
            f"{result['concurrence']:11.6f} {result['chsh_max']:8.6f}"
        )
