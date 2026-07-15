"""Diagonal minisuperspace reduction of a ghost-free bimetric potential."""

from compare_models import evaluate


def elementary_invariants(lapse_ratio: float, scale_ratio: float) -> tuple[float, ...]:
    n, r = lapse_ratio, scale_ratio
    return (1.0, n + 3*r, 3*n*r + 3*r**2, 3*n*r**2 + r**3, n*r**3)


def potential(n: float, r: float, beta=(0.0, 1.0, -4.0/3.0, 1.0, 0.0)) -> float:
    return sum(b*e for b, e in zip(beta, elementary_invariants(n, r)))


def effective_coupling(r: float, n: float = 1.0, alpha: float = 0.05) -> float:
    h = 1e-6
    derivative = (potential(n, r*(1+h)) - potential(n, r*(1-h))) / (2*h)
    return alpha * derivative


if __name__ == "__main__":
    print("r potential coupling concurrence chsh_max")
    for r in (1.0, 1.2, 1.5):
        coupling = effective_coupling(r)
        result = evaluate(omega_minus=1.0, coupling=coupling)
        print(f"{r:3.1f} {potential(1.0,r):9.6f} {coupling:8.6f} {result['concurrence']:11.6f} {result['chsh_max']:8.6f}")
