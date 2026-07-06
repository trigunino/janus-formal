"""SI density normalization from Z2/Sigma dimensionless invariants."""

from __future__ import annotations

import math

from .constants import SPEED_OF_LIGHT_KM_S
from .physical_units import MPC_IN_METERS


def baryon_density_from_r3_invariant(
    baryon_number_density0_times_r_curv3: float,
    r_curv_m: float,
) -> float:
    value = float(baryon_number_density0_times_r_curv3)
    radius = float(r_curv_m)
    if not math.isfinite(value) or value <= 0.0:
        raise ValueError("baryon_number_density0_times_r_curv3 must be positive and finite")
    if not math.isfinite(radius) or radius <= 0.0:
        raise ValueError("r_curv_m must be positive and finite")
    return value / radius**3


def baryon_density_from_hubble_volume_invariant(
    baryon_number_density0_times_hubble_volume: float,
    h0_km_s_mpc: float,
) -> float:
    value = float(baryon_number_density0_times_hubble_volume)
    h0 = float(h0_km_s_mpc)
    if not math.isfinite(value) or value <= 0.0:
        raise ValueError("baryon_number_density0_times_hubble_volume must be positive and finite")
    if not math.isfinite(h0) or h0 <= 0.0:
        raise ValueError("h0_km_s_mpc must be positive and finite")
    hubble_length_m = SPEED_OF_LIGHT_KM_S / h0 * MPC_IN_METERS
    return value / hubble_length_m**3
