"""Conditional PT-even Landau phase-transition diagnostics."""

from __future__ import annotations

import numpy as np


def potential(phi: np.ndarray | float, a: float, b: float) -> np.ndarray:
    value = np.asarray(phi, dtype=float)
    return a * value**2 + b * value**4


def stationary_points(a: float, b: float) -> np.ndarray:
    if b <= 0:
        raise ValueError("bounded quartic model requires b>0")
    if a >= 0:
        return np.array([0.0])
    scale = np.sqrt(-a / (2.0 * b))
    return np.array([-scale, 0.0, scale])


def curvature(phi: np.ndarray | float, a: float, b: float) -> np.ndarray:
    value = np.asarray(phi, dtype=float)
    return 2.0 * a + 12.0 * b * value**2


def classify_stationary_points(a: float, b: float) -> list[dict[str, float | str]]:
    points = stationary_points(a, b)
    result = []
    for point in points:
        second = float(curvature(point, a, b))
        kind = "minimum" if second > 0 else "maximum" if second < 0 else "marginal"
        result.append(
            {
                "phi": float(point),
                "potential": float(potential(point, a, b)),
                "curvature": second,
                "kind": kind,
            }
        )
    return result


def thermal_quadratic_coefficient(
    temperature: np.ndarray | float, coefficient: float, critical_temperature: float
) -> np.ndarray:
    if coefficient <= 0 or critical_temperature < 0:
        raise ValueError("coefficient must be positive and critical temperature nonnegative")
    value = np.asarray(temperature, dtype=float)
    return coefficient * (value**2 - critical_temperature**2)


def equilibrium_order_parameter(
    temperature: np.ndarray | float,
    thermal_coefficient: float,
    critical_temperature: float,
    quartic: float,
) -> np.ndarray:
    a = thermal_quadratic_coefficient(temperature, thermal_coefficient, critical_temperature)
    if quartic <= 0:
        raise ValueError("quartic must be positive")
    return np.sqrt(np.maximum(-a / (2.0 * quartic), 0.0))


def scale_selection_audit(a: float | None, b: float | None) -> dict:
    ready = a is not None and b is not None and b > 0 and a < 0
    return {
        "pt_even_form_known": True,
        "quadratic_coefficient_supplied": a is not None,
        "quartic_coefficient_supplied": b is not None,
        "nonzero_scale_selected": ready,
        "broken_scale": np.sqrt(-a / (2.0 * b)) if ready else None,
        "verdict": (
            "scale_comes_from_coefficient_ratio_not_from_PT"
            if ready
            else "PT_symmetry_alone_does_not_select_nonzero_scale"
        ),
    }
