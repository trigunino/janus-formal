"""1+1D reduction of the exploratory bimetric potential."""

from action_ansatz import induced_coupling_from_action, potential


def d_potential_dc(c: float, beta: float = 0.1) -> float:
    """Analytic variation of U=beta/2*(c^2-1)^2."""
    return induced_coupling_from_action(c, beta)


def finite_difference(c: float, beta: float = 0.1, step: float = 1e-6) -> float:
    return (potential(c + step, beta) - potential(c - step, beta)) / (2.0 * step)


if __name__ == "__main__":
    for c in (0.8, 1.0, 1.2):
        analytic = d_potential_dc(c)
        numeric = finite_difference(c)
        print(c, analytic, numeric, abs(analytic - numeric))
