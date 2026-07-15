"""Minisuperspace reduction with two scale factors."""

from compare_models import evaluate


def interaction_potential(r: float, beta: float = 0.1) -> float:
    return 0.5 * beta * (r - 1.0 / r) ** 2


def induced_coupling(r: float, alpha: float = 0.2) -> float:
    # Derivative of the symmetric potential with respect to log(r).
    return alpha * (r**2 - 1.0 / (r**2))


if __name__ == "__main__":
    print("ratio potential coupling concurrence chsh_max")
    for ratio in (1.0, 1.2, 1.5, 1.0 / 1.5):
        coupling = induced_coupling(ratio)
        result = evaluate(omega_minus=1.0, coupling=coupling)
        print(f"{ratio:5.2f} {interaction_potential(ratio):9.6f} {coupling:8.6f} {result['concurrence']:11.6f} {result['chsh_max']:8.6f}")
