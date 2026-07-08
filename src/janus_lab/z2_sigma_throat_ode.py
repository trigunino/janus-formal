"""Minimal throat ODE analysis for the regular Z2/Sigma local collar."""

from __future__ import annotations

import math

import numpy as np


def _checked_rho_grid(rho_grid) -> np.ndarray:
    grid = np.asarray(rho_grid, dtype=float)
    if grid.ndim != 1 or grid.size < 2:
        raise ValueError("rho_grid must be one-dimensional with at least two points")
    if not np.all(np.isfinite(grid)):
        raise ValueError("rho_grid must be finite")
    if np.any(grid < 0.0) or np.any(np.diff(grid) <= 0.0):
        raise ValueError("rho_grid must start at rho>=0 and be strictly increasing")
    return grid


def _checked_r0_values(R0_values) -> np.ndarray:
    values = np.asarray(R0_values, dtype=float)
    if values.ndim != 1 or values.size == 0:
        raise ValueError("R0_values must be a nonempty one-dimensional array")
    if not np.all(np.isfinite(values)) or np.any(values <= 0.0):
        raise ValueError("R0_values must be finite and strictly positive")
    return values


def normalized_throat_profile(rho) -> np.ndarray:
    rho_arr = np.asarray(rho, dtype=float)
    return 1.0 + np.log(np.cosh(rho_arr))


def normalized_throat_profile_prime(rho) -> np.ndarray:
    rho_arr = np.asarray(rho, dtype=float)
    return np.tanh(rho_arr)


def normalized_throat_profile_second(rho) -> np.ndarray:
    rho_arr = np.asarray(rho, dtype=float)
    return np.cosh(rho_arr) ** (-2.0)


def normalized_throat_ode_residual(rho) -> np.ndarray:
    profile = normalized_throat_profile(rho)
    second = normalized_throat_profile_second(rho)
    return second - np.exp(2.0 - 2.0 * profile)


def solve_minimal_ci_throat_family(*, rho_grid, R0_values) -> dict:
    """Solve the normalized throat ODE and expose the physical R0 degeneracy.

    The local MPLA/Z2 throat profile satisfies
        r''(rho) = exp(2 - 2 r(rho)),
    with minimal normalized initial conditions
        r(0) = 1,  r'(0) = 0.

    The closed-form solution is unique at the normalized level:
        r(rho) = 1 + log(cosh(rho)).

    The physical radius family is then
        R(rho) = R0 * r(rho),
    so the local ODE fixes the shape but not the absolute scale R0.
    """

    grid = _checked_rho_grid(rho_grid)
    r0_values = _checked_r0_values(R0_values)

    normalized = normalized_throat_profile(grid)
    normalized_prime = normalized_throat_profile_prime(grid)
    normalized_second = normalized_throat_profile_second(grid)
    residual = normalized_throat_ode_residual(grid)

    family = []
    for r0 in r0_values:
        radius = float(r0) * normalized
        family.append(
            {
                "R0": float(r0),
                "R_of_rho": radius.tolist(),
                "R_prime_of_rho": (float(r0) * normalized_prime).tolist(),
                "R_second_of_rho": (float(r0) * normalized_second).tolist(),
            }
        )

    first = family[0]["R_of_rho"]
    distinct_profiles = any(
        any(not math.isclose(a, b, rel_tol=1.0e-12, abs_tol=1.0e-12) for a, b in zip(first, item["R_of_rho"]))
        for item in family[1:]
    )
    normalized_reconstruction_error = max(
        float(np.max(np.abs(np.asarray(item["R_of_rho"], dtype=float) / item["R0"] - normalized)))
        for item in family
    )

    return {
        "active_core": "Z2_tunnel_Sigma",
        "branch": "regular_non_null_Sigma",
        "local_model": "MPLA_schwarzschild_throat_normalized",
        "normalized_ode": "r''(rho) = exp(2 - 2 r(rho))",
        "minimal_normalized_initial_conditions": {
            "r(0)": 1.0,
            "r'(0)": 0.0,
        },
        "normalized_solution_closed_form": "r(rho) = 1 + log(cosh(rho))",
        "rho_grid": grid.tolist(),
        "normalized_profile": normalized.tolist(),
        "normalized_profile_prime": normalized_prime.tolist(),
        "normalized_profile_second": normalized_second.tolist(),
        "normalized_ode_residual_max_abs": float(np.max(np.abs(residual))),
        "normalized_solution_unique_under_minimal_CI": True,
        "throat_is_minimal": bool(
            math.isclose(float(normalized[0]), 1.0, rel_tol=0.0, abs_tol=1.0e-12)
            and math.isclose(float(normalized_prime[0]), 0.0, rel_tol=0.0, abs_tol=1.0e-12)
            and float(normalized_second[0]) > 0.0
        ),
        "physical_radius_family": "R(rho) = R0 * r(rho)",
        "R0_values": r0_values.tolist(),
        "physical_profiles": family,
        "R0_unique": False,
        "R0_scale_degenerate": True,
        "scale_degeneracy_reason": (
            "The normalized ODE and minimal normalized initial conditions fix only the "
            "dimensionless shape r(rho). Every R0>0 generates a distinct physical "
            "solution R(rho)=R0*r(rho) with the same normalized orbit."
        ),
        "distinct_physical_profiles_sampled": distinct_profiles,
        "normalized_reconstruction_error_max_abs": normalized_reconstruction_error,
    }
