from __future__ import annotations

import json
import math
from dataclasses import asdict, dataclass


@dataclass(frozen=True)
class CutoffDiagnostic:
    l_max: int
    n_max: int
    minimizing_modulus: float
    minimum_at_upper_grid_boundary: bool
    strictly_decreasing_on_grid: bool
    value_at_lower_boundary: float
    value_at_upper_boundary: float


@dataclass(frozen=True)
class NaiveDeterminantNoGoAudit:
    lower_modulus: float
    upper_modulus: float
    grid_points: int
    circle_twist: float
    dimensionless_mass_squared: float
    cutoff_diagnostics: tuple[CutoffDiagnostic, ...]
    all_minima_at_upper_boundary: bool
    all_grids_strictly_decreasing: bool
    cutoff_spread_at_upper_boundary: float
    conclusion: str


def truncated_scalar_log_determinant(
    modulus: float,
    *,
    l_max: int,
    n_max: int,
    circle_twist: float,
    mass_squared: float,
) -> float:
    """Unrenormalized finite-mode proxy on S2 x S1.

    Eigenvalues are

        l(l+1) + (2*pi*(n+a)/T)^2 + m^2,

    with scalar S2 degeneracy 2*l+1.  This is deliberately *not* interpreted as
    a physical effective action: it lacks heat-kernel subtraction, local
    counterterms, gauge/ghost sectors and a volume convention.
    """

    if modulus <= 0.0:
        raise ValueError("modulus must be positive")
    if l_max < 0 or n_max < 0:
        raise ValueError("cutoffs must be nonnegative")
    if mass_squared <= 0.0:
        raise ValueError("a positive regulator mass is required")

    total = 0.0
    for ell in range(l_max + 1):
        degeneracy = 2 * ell + 1
        sphere_eigenvalue = ell * (ell + 1)
        for mode in range(-n_max, n_max + 1):
            circle_eigenvalue = (
                2.0 * math.pi * (mode + circle_twist) / modulus
            ) ** 2
            eigenvalue = sphere_eigenvalue + circle_eigenvalue + mass_squared
            total += 0.5 * degeneracy * math.log(eigenvalue)
    return total


def build_audit(
    *,
    lower_modulus: float = 1.0,
    upper_modulus: float = 20.0,
    grid_points: int = 160,
    circle_twist: float = 0.5,
    mass_squared: float = 0.1,
) -> NaiveDeterminantNoGoAudit:
    if not (0.0 < lower_modulus < upper_modulus):
        raise ValueError("require 0 < lower_modulus < upper_modulus")
    if grid_points < 3:
        raise ValueError("at least three grid points are required")

    moduli = [
        lower_modulus
        + (upper_modulus - lower_modulus) * index / (grid_points - 1)
        for index in range(grid_points)
    ]
    cutoffs = ((3, 5), (5, 10), (8, 16))
    diagnostics: list[CutoffDiagnostic] = []

    for l_max, n_max in cutoffs:
        values = [
            truncated_scalar_log_determinant(
                modulus,
                l_max=l_max,
                n_max=n_max,
                circle_twist=circle_twist,
                mass_squared=mass_squared,
            )
            for modulus in moduli
        ]
        minimizing_index = min(range(len(values)), key=values.__getitem__)
        strictly_decreasing = all(
            later < earlier for earlier, later in zip(values, values[1:])
        )
        diagnostics.append(
            CutoffDiagnostic(
                l_max=l_max,
                n_max=n_max,
                minimizing_modulus=moduli[minimizing_index],
                minimum_at_upper_grid_boundary=(
                    minimizing_index == len(moduli) - 1
                ),
                strictly_decreasing_on_grid=strictly_decreasing,
                value_at_lower_boundary=values[0],
                value_at_upper_boundary=values[-1],
            )
        )

    upper_values = [item.value_at_upper_boundary for item in diagnostics]
    return NaiveDeterminantNoGoAudit(
        lower_modulus=lower_modulus,
        upper_modulus=upper_modulus,
        grid_points=grid_points,
        circle_twist=circle_twist,
        dimensionless_mass_squared=mass_squared,
        cutoff_diagnostics=tuple(diagnostics),
        all_minima_at_upper_boundary=all(
            item.minimum_at_upper_grid_boundary for item in diagnostics
        ),
        all_grids_strictly_decreasing=all(
            item.strictly_decreasing_on_grid for item in diagnostics
        ),
        cutoff_spread_at_upper_boundary=max(upper_values) - min(upper_values),
        conclusion=(
            "The raw finite-mode log determinant is monotone over the tested "
            "range and strongly cutoff dependent. It cannot select the Janus "
            "circle modulus. A physical calculation must specify heat-kernel "
            "subtractions, local counterterms, field/ghost content and a "
            "renormalization condition before minimization."
        ),
    )


def main() -> int:
    audit = build_audit()
    print(json.dumps(asdict(audit), indent=2, sort_keys=True))
    return 0 if (
        audit.all_minima_at_upper_boundary
        and audit.all_grids_strictly_decreasing
        and audit.cutoff_spread_at_upper_boundary > 1.0
    ) else 1


if __name__ == "__main__":
    raise SystemExit(main())
