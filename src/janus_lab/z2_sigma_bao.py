"""Strict Z2/Sigma BAO calculator.

This module intentionally has no Planck/LCDM defaults. Callers must supply the
active Z2/Sigma expansion function and sound ruler.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Callable

import numpy as np

from .constants import SPEED_OF_LIGHT_KM_S
from .data import BaoDataset


HubbleOfZ = Callable[[np.ndarray], np.ndarray]


@dataclass(frozen=True)
class Z2SigmaBAOResult:
    prediction: np.ndarray
    residual: np.ndarray
    chi2: float


def _as_array(value) -> np.ndarray:
    return np.asarray(value, dtype=float)


def comoving_distance_mpc(
    z: float,
    h_z2sigma: HubbleOfZ,
    samples: int = 4096,
) -> float:
    """Return line-of-sight comoving distance D_C(z), given H_Z2Sigma(z)."""

    if z < 0:
        raise ValueError("Redshift must be non-negative")
    if samples < 8:
        raise ValueError("samples must be >= 8")
    if z == 0:
        return 0.0
    grid = np.linspace(0.0, float(z), samples)
    h_values = _as_array(h_z2sigma(grid))
    if np.any(h_values <= 0) or h_values.shape != grid.shape:
        raise ValueError("H_Z2Sigma(z) must return positive values on the integration grid")
    trapz = np.trapezoid if hasattr(np, "trapezoid") else np.trapz
    return float(SPEED_OF_LIGHT_KM_S * trapz(1.0 / h_values, grid))


def transverse_comoving_distance_mpc(
    z: float,
    h_z2sigma: HubbleOfZ,
    omega_k_z2sigma: float = 0.0,
    h0_z2sigma_km_s_mpc: float | None = None,
    samples: int = 4096,
) -> float:
    """Return active D_M(z), including FLRW curvature when Omega_k is supplied."""

    dc = comoving_distance_mpc(z, h_z2sigma, samples=samples)
    omega_k = float(omega_k_z2sigma)
    if abs(omega_k) < 1.0e-14 or dc == 0.0:
        return dc
    h0 = (
        float(h0_z2sigma_km_s_mpc)
        if h0_z2sigma_km_s_mpc is not None
        else float(_as_array(h_z2sigma(np.asarray([0.0], dtype=float)))[0])
    )
    if h0 <= 0:
        raise ValueError("H0_Z2Sigma must be positive for curved D_M")
    dh0 = SPEED_OF_LIGHT_KM_S / h0
    sqrt_abs_ok = float(np.sqrt(abs(omega_k)))
    argument = sqrt_abs_ok * dc / dh0
    if omega_k > 0:
        return float(dh0 * np.sinh(argument) / sqrt_abs_ok)
    return float(dh0 * np.sin(argument) / sqrt_abs_ok)


def predict_bao_quantity(
    z: float,
    quantity: str,
    h_z2sigma: HubbleOfZ,
    rd_z2sigma_mpc: float,
    omega_k_z2sigma: float = 0.0,
    h0_z2sigma_km_s_mpc: float | None = None,
    samples: int = 4096,
) -> float:
    """Predict a DESI BAO observable from active H_Z2Sigma and r_d."""

    if rd_z2sigma_mpc <= 0:
        raise ValueError("r_d^Z2Sigma must be positive")
    dm = transverse_comoving_distance_mpc(
        z,
        h_z2sigma,
        omega_k_z2sigma=omega_k_z2sigma,
        h0_z2sigma_km_s_mpc=h0_z2sigma_km_s_mpc,
        samples=samples,
    )
    h_at_z = float(_as_array(h_z2sigma(np.asarray([z], dtype=float)))[0])
    if h_at_z <= 0:
        raise ValueError("H_Z2Sigma(z) must be positive")
    dh = SPEED_OF_LIGHT_KM_S / h_at_z

    if quantity == "DM_over_rs":
        return dm / rd_z2sigma_mpc
    if quantity == "DH_over_rs":
        return dh / rd_z2sigma_mpc
    if quantity == "DV_over_rs":
        return float(np.cbrt(float(z) * dm * dm * dh) / rd_z2sigma_mpc)
    raise ValueError(f"Unsupported BAO quantity: {quantity}")


def prediction_vector(
    dataset: BaoDataset,
    h_z2sigma: HubbleOfZ,
    rd_z2sigma_mpc: float,
    omega_k_z2sigma: float = 0.0,
    h0_z2sigma_km_s_mpc: float | None = None,
    samples: int = 4096,
) -> np.ndarray:
    """Predict the DESI vector in dataset order."""

    return np.asarray(
        [
            predict_bao_quantity(
                float(z),
                str(quantity),
                h_z2sigma,
                rd_z2sigma_mpc,
                omega_k_z2sigma=omega_k_z2sigma,
                h0_z2sigma_km_s_mpc=h0_z2sigma_km_s_mpc,
                samples=samples,
            )
            for z, quantity in zip(dataset.z, dataset.quantity)
        ],
        dtype=float,
    )


def chi2_against_desi(
    dataset: BaoDataset,
    h_z2sigma: HubbleOfZ,
    rd_z2sigma_mpc: float,
    omega_k_z2sigma: float = 0.0,
    h0_z2sigma_km_s_mpc: float | None = None,
    samples: int = 4096,
) -> Z2SigmaBAOResult:
    """Evaluate DESI BAO chi2 for supplied active Z2/Sigma functions."""

    prediction = prediction_vector(
        dataset,
        h_z2sigma,
        rd_z2sigma_mpc,
        omega_k_z2sigma=omega_k_z2sigma,
        h0_z2sigma_km_s_mpc=h0_z2sigma_km_s_mpc,
        samples=samples,
    )
    residual = prediction - dataset.value
    chi2 = float(residual @ np.linalg.solve(dataset.covariance, residual))
    return Z2SigmaBAOResult(prediction=prediction, residual=residual, chi2=chi2)


def dimensionless_comoving_distance(
    z: float,
    e_z2sigma: HubbleOfZ,
    samples: int = 4096,
) -> float:
    """Return integral_0^z dz/E_Z2Sigma(z), independent of H0 units."""

    if z < 0:
        raise ValueError("Redshift must be non-negative")
    if samples < 8:
        raise ValueError("samples must be >= 8")
    if z == 0:
        return 0.0
    grid = np.linspace(0.0, float(z), samples)
    e_values = _as_array(e_z2sigma(grid))
    if np.any(e_values <= 0) or e_values.shape != grid.shape:
        raise ValueError("E_Z2Sigma(z) must return positive values on the integration grid")
    trapz = np.trapezoid if hasattr(np, "trapezoid") else np.trapz
    return float(trapz(1.0 / e_values, grid))


def dimensionless_sound_ruler(
    e_z2sigma: HubbleOfZ,
    cs_over_c_z2sigma: HubbleOfZ,
    z_d_z2sigma: float,
    z_max: float = 1.0e7,
    samples: int = 8192,
) -> float:
    """Return H0*r_d/c = integral_zd^inf (c_s/c)/E dz."""

    if z_d_z2sigma <= 0:
        raise ValueError("z_d^Z2Sigma must be positive")
    if z_max <= z_d_z2sigma:
        raise ValueError("z_max must be larger than z_d^Z2Sigma")
    if samples < 16:
        raise ValueError("samples must be >= 16")
    grid = np.geomspace(1.0 + z_d_z2sigma, 1.0 + z_max, samples) - 1.0
    e_values = _as_array(e_z2sigma(grid))
    cs_values = _as_array(cs_over_c_z2sigma(grid))
    if e_values.shape != grid.shape or cs_values.shape != grid.shape:
        raise ValueError("E_Z2Sigma and c_s/c must match the integration grid")
    if np.any(e_values <= 0):
        raise ValueError("E_Z2Sigma(z) must be positive")
    if np.any(cs_values <= 0):
        raise ValueError("c_s^Z2Sigma/c must be positive")
    trapz = np.trapezoid if hasattr(np, "trapezoid") else np.trapz
    return float(trapz(cs_values / e_values, grid))


def dimensionless_transverse_distance(
    z: float,
    e_z2sigma: HubbleOfZ,
    omega_k_z2sigma: float = 0.0,
    samples: int = 4096,
) -> float:
    """Return H0*D_M/c from E_Z2Sigma, including FLRW curvature."""

    dc_hat = dimensionless_comoving_distance(z, e_z2sigma, samples=samples)
    omega_k = float(omega_k_z2sigma)
    if abs(omega_k) < 1.0e-14 or dc_hat == 0.0:
        return dc_hat
    sqrt_abs_ok = float(np.sqrt(abs(omega_k)))
    argument = sqrt_abs_ok * dc_hat
    if omega_k > 0:
        return float(np.sinh(argument) / sqrt_abs_ok)
    return float(np.sin(argument) / sqrt_abs_ok)


def predict_bao_quantity_scale_free(
    z: float,
    quantity: str,
    e_z2sigma: HubbleOfZ,
    rd_hat_z2sigma: float,
    omega_k_z2sigma: float = 0.0,
    samples: int = 4096,
) -> float:
    """Predict BAO ratios from E(z) and H0*r_d/c, without choosing H0."""

    if rd_hat_z2sigma <= 0:
        raise ValueError("H0*r_d^Z2Sigma/c must be positive")
    dm_hat = dimensionless_transverse_distance(
        z,
        e_z2sigma,
        omega_k_z2sigma=omega_k_z2sigma,
        samples=samples,
    )
    e_at_z = float(_as_array(e_z2sigma(np.asarray([z], dtype=float)))[0])
    if e_at_z <= 0:
        raise ValueError("E_Z2Sigma(z) must be positive")
    dh_hat = 1.0 / e_at_z
    if quantity == "DM_over_rs":
        return dm_hat / rd_hat_z2sigma
    if quantity == "DH_over_rs":
        return dh_hat / rd_hat_z2sigma
    if quantity == "DV_over_rs":
        return float(np.cbrt(float(z) * dm_hat * dm_hat * dh_hat) / rd_hat_z2sigma)
    raise ValueError(f"Unsupported BAO quantity: {quantity}")


def prediction_vector_scale_free(
    dataset: BaoDataset,
    e_z2sigma: HubbleOfZ,
    rd_hat_z2sigma: float,
    omega_k_z2sigma: float = 0.0,
    samples: int = 4096,
) -> np.ndarray:
    """Predict the DESI vector in dataset order using only dimensionless inputs."""

    return np.asarray(
        [
            predict_bao_quantity_scale_free(
                float(z),
                str(quantity),
                e_z2sigma,
                rd_hat_z2sigma,
                omega_k_z2sigma=omega_k_z2sigma,
                samples=samples,
            )
            for z, quantity in zip(dataset.z, dataset.quantity)
        ],
        dtype=float,
    )


def chi2_against_desi_scale_free(
    dataset: BaoDataset,
    e_z2sigma: HubbleOfZ,
    rd_hat_z2sigma: float,
    omega_k_z2sigma: float = 0.0,
    samples: int = 4096,
) -> Z2SigmaBAOResult:
    """Evaluate DESI BAO chi2 from dimensionless active Z2/Sigma inputs."""

    prediction = prediction_vector_scale_free(
        dataset,
        e_z2sigma,
        rd_hat_z2sigma,
        omega_k_z2sigma=omega_k_z2sigma,
        samples=samples,
    )
    residual = prediction - dataset.value
    chi2 = float(residual @ np.linalg.solve(dataset.covariance, residual))
    return Z2SigmaBAOResult(prediction=prediction, residual=residual, chi2=chi2)
