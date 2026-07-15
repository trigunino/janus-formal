"""Lapse-constraint and local stability checks for the tuned branch."""

from hassan_rosen_minisuperspace import potential


def lapse_constraint(r: float, h: float = 1e-6) -> float:
    """Derivative of the potential with respect to lapse ratio."""
    return (potential(1.0 + h, r) - potential(1.0 - h, r)) / (2.0 * h)


def radial_hessian(r: float = 1.0, h: float = 1e-4) -> float:
    return (potential(1.0, r + h) - 2.0 * potential(1.0, r) + potential(1.0, r - h)) / (h * h)


if __name__ == "__main__":
    print({
        "lapse_constraint_at_symmetric_branch": lapse_constraint(1.0),
        "radial_hessian_at_symmetric_branch": radial_hessian(),
    })
    assert abs(lapse_constraint(1.0)) < 1e-10
    assert radial_hessian() > 0.0
