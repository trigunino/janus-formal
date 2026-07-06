"""Minimal Z2/Sigma counterterm coefficient solver."""

from __future__ import annotations

import numpy as np


def solve_minimal_counterterm_coefficients(
    *,
    R_Sigma_values,
    R_h_trace_values,
    R_K_trace_values,
    kappa_Z2Sigma: float,
    z2_orientation_sign: float,
    sqrt_det_q: float = 1.0,
    noncartan_values=None,
    enforce_linear_k_partition: bool = False,
) -> dict:
    radius = np.asarray(R_Sigma_values, dtype=float)
    r_h = np.asarray(R_h_trace_values, dtype=float)
    r_k = np.asarray(R_K_trace_values, dtype=float)
    if radius.ndim != 1 or radius.size < 1:
        raise ValueError("R_Sigma_values must be one-dimensional")
    if np.any(radius <= 0.0) or not np.all(np.isfinite(radius)):
        raise ValueError("R_Sigma_values must be finite and positive")
    if r_h.shape != radius.shape or r_k.shape != radius.shape:
        raise ValueError("trace values must align with R_Sigma_values")
    if not np.all(np.isfinite(r_h)) or not np.all(np.isfinite(r_k)):
        raise ValueError("trace values must be finite")
    eps = float(z2_orientation_sign)
    if eps not in (-1.0, 1.0):
        raise ValueError("z2_orientation_sign must be +1.0 or -1.0")
    kappa = float(kappa_Z2Sigma)
    if not np.isfinite(kappa) or kappa <= 0.0:
        raise ValueError("kappa_Z2Sigma must be positive")
    sqrt_q = float(sqrt_det_q)
    if not np.isfinite(sqrt_q) or sqrt_q <= 0.0:
        raise ValueError("sqrt_det_q must be positive")
    noncartan = (
        np.zeros_like(radius)
        if noncartan_values is None
        else np.asarray(noncartan_values, dtype=float)
    )
    if noncartan.shape != radius.shape or not np.all(np.isfinite(noncartan)):
        raise ValueError("noncartan_values must align with R_Sigma_values")

    coeffs = []
    residuals = []
    for R, h_trace, k_trace, e_noncartan in zip(radius, r_h, r_k, noncartan):
        full_matrix = np.asarray(
            [
                [-3.0 * eps / R**2, -18.0 / R**3, 0.0],
                [3.0 * eps / R, 18.0 / R**2, 6.0 / R**2],
                [6.0 * eps * R, 9.0, 6.0],
            ],
            dtype=float,
        )
        rhs = np.asarray(
            [
                k_trace,
                h_trace,
                (-6.0 * eps * sqrt_q * R / kappa - e_noncartan) / sqrt_q,
            ],
            dtype=float,
        )
        if enforce_linear_k_partition:
            reduced = full_matrix[:, 1:]
            reduced_coeff, *_ = np.linalg.lstsq(reduced, rhs, rcond=None)
            coeff = np.asarray([0.0, *reduced_coeff], dtype=float)
        else:
            coeff = np.linalg.solve(full_matrix, rhs)
        coeffs.append(coeff)
        residuals.append(full_matrix @ coeff - rhs)

    coeff_arr = np.asarray(coeffs, dtype=float)
    residual_arr = np.asarray(residuals, dtype=float)
    spread = np.ptp(coeff_arr, axis=0) if coeff_arr.shape[0] > 1 else np.zeros(3)
    return {
        "c1_values": coeff_arr[:, 0].tolist(),
        "c2_values": coeff_arr[:, 1].tolist(),
        "c3_values": coeff_arr[:, 2].tolist(),
        "linear_system_residual_max_abs": float(np.max(np.abs(residual_arr))),
        "constant_coefficient_spread": {
            "c1": float(spread[0]),
            "c2": float(spread[1]),
            "c3": float(spread[2]),
        },
        "constant_coefficients_consistent": bool(np.all(spread <= 1.0e-10)),
        "coefficient_status": "constant" if np.all(spread <= 1.0e-10) else "pointwise_function",
        "linear_K_partition_enforced": bool(enforce_linear_k_partition),
        "c1_zero_after_partition": bool(
            enforce_linear_k_partition and np.all(np.abs(coeff_arr[:, 0]) <= 1.0e-12)
        ),
        "equations": [
            "R_K_trace = -3 eps c1/R^2 - 18 c2/R^3",
            "R_h_trace = 3 eps c1/R + (18 c2 + 6 c3)/R^2",
            "0 = E_CartanGHY + E_counterterm + E_noncartan",
        ],
    }
