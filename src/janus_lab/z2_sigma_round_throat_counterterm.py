from __future__ import annotations

from dataclasses import dataclass

import numpy as np


@dataclass(frozen=True)
class RoundThroatCountertermCoefficients:
    a0: float
    a1: float
    a2: float
    a3: float
    epsilon_z2: float
    sqrt_det_q: float = 1.0


def round_throat_lct_values(
    radius: list | np.ndarray,
    coeff: RoundThroatCountertermCoefficients,
) -> np.ndarray:
    r = np.asarray(radius, dtype=float)
    if np.any(r <= 0.0) or not np.all(np.isfinite(r)):
        raise ValueError("radius values must be positive and finite")
    eps = float(coeff.epsilon_z2)
    if eps not in (-1.0, 1.0):
        raise ValueError("epsilon_z2 must be +1 or -1")
    return coeff.a0 + 3.0 * eps * coeff.a1 / r + (9.0 * coeff.a2 + 3.0 * coeff.a3) / r**2


def round_throat_e_counterterm_values(
    radius: list | np.ndarray,
    coeff: RoundThroatCountertermCoefficients,
) -> np.ndarray:
    """Return partial_R(sqrt|h| L_ct) for h_ab=diag(-1,R^2 q_ij).

    With K_tau=0, K_s=epsilon/R:
      L_ct = a0 + 3 eps a1/R + (9 a2 + 3 a3)/R^2
      sqrt|h| = R^3 sqrt(det q)
      E_ct = sqrt(det q) * (3 a0 R^2 + 6 eps a1 R + 9 a2 + 3 a3)
    """

    r = np.asarray(radius, dtype=float)
    if np.any(r <= 0.0) or not np.all(np.isfinite(r)):
        raise ValueError("radius values must be positive and finite")
    eps = float(coeff.epsilon_z2)
    if eps not in (-1.0, 1.0):
        raise ValueError("epsilon_z2 must be +1 or -1")
    if coeff.sqrt_det_q <= 0.0 or not np.isfinite(coeff.sqrt_det_q):
        raise ValueError("sqrt_det_q must be positive and finite")
    return coeff.sqrt_det_q * (
        3.0 * coeff.a0 * r**2
        + 6.0 * eps * coeff.a1 * r
        + 9.0 * coeff.a2
        + 3.0 * coeff.a3
    )


def positive_round_throat_radius_roots(
    *,
    coeff: RoundThroatCountertermCoefficients,
    e_other: float = 0.0,
    tolerance: float = 1e-12,
) -> list[float]:
    """Solve E_counterterm(R)+e_other=0 for positive real R."""

    eps = float(coeff.epsilon_z2)
    if eps not in (-1.0, 1.0):
        raise ValueError("epsilon_z2 must be +1 or -1")
    if coeff.sqrt_det_q <= 0.0 or not np.isfinite(coeff.sqrt_det_q):
        raise ValueError("sqrt_det_q must be positive and finite")
    a = coeff.sqrt_det_q * 3.0 * coeff.a0
    b = coeff.sqrt_det_q * 6.0 * eps * coeff.a1
    c = coeff.sqrt_det_q * (9.0 * coeff.a2 + 3.0 * coeff.a3) + float(e_other)
    if not np.all(np.isfinite([a, b, c])):
        raise ValueError("quadratic coefficients must be finite")
    roots: list[float] = []
    if abs(a) <= tolerance:
        if abs(b) <= tolerance:
            return []
        root = -c / b
        return [float(root)] if root > tolerance and np.isfinite(root) else []
    disc = b * b - 4.0 * a * c
    if disc < -tolerance:
        return []
    disc = max(0.0, disc)
    sqrt_disc = float(np.sqrt(disc))
    for root in [(-b - sqrt_disc) / (2.0 * a), (-b + sqrt_disc) / (2.0 * a)]:
        if root > tolerance and np.isfinite(root):
            roots.append(float(root))
    return sorted(set(round(root, 15) for root in roots))


def no_extension_zero_source_constraints() -> dict:
    """Return the round-throat no-extension coefficient constraints.

    For L_ct = a0 + a1 K + a2 K^2 + a3 K_ab K^ab on the round Z2 throat,
    E_ct = sqrt(det q) * (3 a0 R^2 + 6 eps a1 R + 9 a2 + 3 a3).
    With zero Holst/Nieh-Yan and matter-flux radial blocks, vanishing for every
    positive R forces the polynomial coefficients to vanish term by term.
    """

    return {
        "polynomial": "3 a0 R^2 + 6 epsilon_Z2 a1 R + 9 a2 + 3 a3",
        "zero_for_all_positive_R_constraints": {
            "a0": "0",
            "a1": "0",
            "a3": "-3*a2",
        },
        "remaining_free_symbol": "a2",
        "counterterm_density_on_round_throat": "0",
        "E_counterterm_on_round_throat": "0",
        "radius_selected": False,
        "interpretation": (
            "The remaining a2 direction cancels out of L_ct and E_ct on the "
            "round throat. It cannot fix R_Sigma."
        ),
    }
