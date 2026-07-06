"""Dimensionless Z2/Sigma Noether density reductions."""

from __future__ import annotations

import math


def dimensionless_noether_density_r3(
    projected_charge: float,
    *,
    quotient_spatial_slice: str = "RP3",
) -> dict:
    charge = float(projected_charge)
    if not math.isfinite(charge) or charge <= 0.0:
        raise ValueError("projected_charge must be positive and finite")
    if quotient_spatial_slice == "RP3":
        volume_factor = 1.0
    elif quotient_spatial_slice == "S3_paired_leaf_representative":
        volume_factor = 2.0
    else:
        raise ValueError("quotient_spatial_slice must be RP3 or S3_paired_leaf_representative")
    return {
        "projected_baryon_number_charge_Z2Sigma": charge,
        "quotient_spatial_slice": quotient_spatial_slice,
        "volume_factor_pi2_R3": volume_factor,
        "formula": "n_b0_Z2Sigma * R_curv_Z2Sigma^3 = N_b,Z2Sigma/(volume_factor*pi^2)",
        "baryon_number_density0_times_Rcurv3_Z2Sigma": charge / (volume_factor * math.pi**2),
    }


def hubble_volume_noether_density(
    baryon_number_density0_times_Rcurv3: float,
    h0_r_curv_over_c: float,
) -> dict:
    density_r3 = float(baryon_number_density0_times_Rcurv3)
    scale = float(h0_r_curv_over_c)
    if not math.isfinite(density_r3) or density_r3 <= 0.0:
        raise ValueError("baryon_number_density0_times_Rcurv3 must be positive and finite")
    if not math.isfinite(scale) or scale <= 0.0:
        raise ValueError("h0_r_curv_over_c must be positive and finite")
    return {
        "formula": "n_b0_Z2Sigma*(c/H0_Z2Sigma)^3 = (n_b0_Z2Sigma*R_curv_Z2Sigma^3)/(H0_Z2Sigma*R_curv_Z2Sigma/c)^3",
        "baryon_number_density0_times_Hubble_volume_Z2Sigma": density_r3 / scale**3,
        "h0_R_curv_over_c_Z2Sigma": scale,
    }
