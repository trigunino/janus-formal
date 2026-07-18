from __future__ import annotations

import numpy as np


def infinity_norm(matrix: np.ndarray) -> float:
    return float(np.max(np.sum(np.abs(matrix), axis=1)))


def proportional_tube_certificate(matrix: np.ndarray, c: float) -> dict:
    if c <= 0:
        raise ValueError("c must be positive")
    matrix = np.asarray(matrix, dtype=float)
    if matrix.ndim != 2 or matrix.shape[0] != matrix.shape[1]:
        raise ValueError("matrix must be square")
    radius = infinity_norm(matrix - c**2 * np.eye(matrix.shape[0]))
    margin = c**2 - radius
    return {
        "radius": radius,
        "right_half_plane_margin": margin,
        "principal_root_certified": margin > 0,
    }


def evolution_budget_certificate(c: float, initial_radius: float, integrated_speed: float) -> dict:
    if min(c, initial_radius, integrated_speed) < 0 or c == 0:
        raise ValueError("invalid nonnegative evolution budget")
    margin = c**2 - initial_radius - integrated_speed
    return {"remaining_margin": margin, "tube_preserved": margin > 0}


def build_payload() -> dict:
    return {
        "artifact": "bimetric_real_square_root_domain",
        "status": "spectral_admissibility_domain_classified",
        "matrix": "A=g_plus^{-1} g_minus",
        "principal_real_root_sufficient_domain": "spectrum(A) avoids the closed negative real axis",
        "general_real_root_criterion": "for every negative real eigenvalue, Jordan blocks of each size occur an even number of times",
        "branch": {
            "proportional_positive": "A=c^2 I with c>0 is admissible and sqrt(A)=c I",
            "boundary": "an eigenvalue reaching the negative real axis is a branch/domain boundary",
            "quantitative_tube": "||A-c^2 I||_infinity<c^2 implies Re spectrum(A)>0",
            "evolution_budget": "||A(0)-c^2 I||_infinity+integral ||A_dot||_infinity dt<c^2",
            "program_p_global_diagonal_sector": "positive smooth diagonal scales give positive eigenvalue ratios and a global smooth principal root",
        },
        "closure": {
            "pointwise_spectral_domain_classified": True,
            "positive_proportional_branch_in_domain": True,
            "local_quantitative_tube_proved": True,
            "conditional_evolution_preservation_proved": True,
            "global_positive_diagonal_sector_root_proved_by_program_p": True,
            "global_general_lorentz_root_proved": False,
            "global_spacetime_avoidance_proved": False,
            "evolution_preserves_domain": False,
        },
    }
