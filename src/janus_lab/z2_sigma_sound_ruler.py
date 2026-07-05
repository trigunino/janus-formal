"""Strict Z2/Sigma sound-ruler integration."""

from __future__ import annotations

from typing import Callable

import numpy as np


FunctionOfZ = Callable[[np.ndarray], np.ndarray]


def evaluate_rd_z2sigma_mpc(
    h_z2sigma: FunctionOfZ,
    cs_z2sigma_km_s: FunctionOfZ,
    z_d_z2sigma: float,
    z_max: float = 1.0e7,
    samples: int = 8192,
) -> float:
    """Evaluate r_d^Z2Sigma = integral_zd^inf c_s(z)/H(z) dz.

    The upper limit is finite and explicit. No fitted Planck/LCDM ruler is used.
    """

    if z_d_z2sigma <= 0:
        raise ValueError("z_d^Z2Sigma must be positive")
    if z_max <= z_d_z2sigma:
        raise ValueError("z_max must be larger than z_d^Z2Sigma")
    if samples < 16:
        raise ValueError("samples must be >= 16")

    grid = np.geomspace(1.0 + z_d_z2sigma, 1.0 + z_max, samples) - 1.0
    h_values = np.asarray(h_z2sigma(grid), dtype=float)
    cs_values = np.asarray(cs_z2sigma_km_s(grid), dtype=float)
    if h_values.shape != grid.shape or cs_values.shape != grid.shape:
        raise ValueError("H_Z2Sigma and c_s^Z2Sigma must match the integration grid")
    if np.any(h_values <= 0):
        raise ValueError("H_Z2Sigma(z) must be positive")
    if np.any(cs_values <= 0):
        raise ValueError("c_s^Z2Sigma(z) must be positive")

    trapz = np.trapezoid if hasattr(np, "trapezoid") else np.trapz
    return float(trapz(cs_values / h_values, grid))
