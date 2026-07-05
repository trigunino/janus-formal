"""Strict active Z2/Sigma background helpers."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Callable

import numpy as np

from .constants import SPEED_OF_LIGHT_KM_S


FunctionOfA = Callable[[np.ndarray], np.ndarray]


def omega_k_from_flrw_curvature_radius(
    h0_z2sigma_km_s_mpc: float,
    curvature_radius_mpc: float,
    curvature_sign_k: int,
) -> float:
    """Return Omega_k = -k c^2 / (H0^2 R_curv^2) from active FLRW curvature data."""

    if h0_z2sigma_km_s_mpc <= 0.0:
        raise ValueError("h0_z2sigma_km_s_mpc must be positive")
    if curvature_sign_k not in (-1, 0, 1):
        raise ValueError("curvature_sign_k must be -1, 0 or 1")
    if curvature_sign_k == 0:
        return 0.0
    if curvature_radius_mpc <= 0.0:
        raise ValueError("curvature_radius_mpc must be positive for non-flat curvature")
    return -float(curvature_sign_k) * (
        SPEED_OF_LIGHT_KM_S / (float(h0_z2sigma_km_s_mpc) * float(curvature_radius_mpc))
    ) ** 2


def omega_k_from_dimensionless_curvature_scale(
    h0_r_curv_over_c: float,
    curvature_sign_k: int,
) -> float:
    """Return Omega_k = -k/(H0 R_curv/c)^2 for scale-free BAO inputs."""

    if curvature_sign_k not in (-1, 0, 1):
        raise ValueError("curvature_sign_k must be -1, 0 or 1")
    if curvature_sign_k == 0:
        return 0.0
    if h0_r_curv_over_c <= 0.0:
        raise ValueError("h0_r_curv_over_c must be positive for non-flat curvature")
    return -float(curvature_sign_k) / float(h0_r_curv_over_c) ** 2


def dimensionless_curvature_scale_from_h0_radius(
    h0_z2sigma_km_s_mpc: float,
    curvature_radius_mpc: float,
) -> float:
    """Return H0_Z2Sigma R_curv_Z2Sigma / c from active scalar inputs."""

    if h0_z2sigma_km_s_mpc <= 0.0:
        raise ValueError("h0_z2sigma_km_s_mpc must be positive")
    if curvature_radius_mpc <= 0.0:
        raise ValueError("curvature_radius_mpc must be positive")
    return float(h0_z2sigma_km_s_mpc) * float(curvature_radius_mpc) / SPEED_OF_LIGHT_KM_S


@dataclass(frozen=True)
class EffectiveFluidComponents:
    """Active FLRW rho/p components normalized to rho_crit0."""

    cartan_ghy_rho: FunctionOfA
    cartan_ghy_p: FunctionOfA
    holst_nieh_yan_rho: FunctionOfA
    holst_nieh_yan_p: FunctionOfA
    matter_flux_rho: FunctionOfA
    matter_flux_p: FunctionOfA
    counterterm_rho: FunctionOfA
    counterterm_p: FunctionOfA


def _component_sum(a: np.ndarray, functions: tuple[FunctionOfA, ...], label: str) -> np.ndarray:
    total = np.zeros_like(a, dtype=float)
    for function in functions:
        values = np.asarray(function(a), dtype=float)
        if values.shape != a.shape:
            raise ValueError(f"{label} component shape must match scale-factor input")
        if not np.all(np.isfinite(values)):
            raise ValueError(f"{label} components must be finite")
        total = total + values
    return total


def make_effective_fluid_functions(
    components: EffectiveFluidComponents,
) -> tuple[FunctionOfA, FunctionOfA]:
    """Assemble active rho_eff(a), p_eff(a) from supplied FLRW components."""

    def rho_eff(a):
        a_arr = np.asarray(a, dtype=float)
        if np.any(a_arr <= 0):
            raise ValueError("Scale factor must be positive")
        return _component_sum(
            a_arr,
            (
                components.cartan_ghy_rho,
                components.holst_nieh_yan_rho,
                components.matter_flux_rho,
                components.counterterm_rho,
            ),
            "rho_eff_Z2Sigma",
        )

    def p_eff(a):
        a_arr = np.asarray(a, dtype=float)
        if np.any(a_arr <= 0):
            raise ValueError("Scale factor must be positive")
        return _component_sum(
            a_arr,
            (
                components.cartan_ghy_p,
                components.holst_nieh_yan_p,
                components.matter_flux_p,
                components.counterterm_p,
            ),
            "p_eff_Z2Sigma",
        )

    return rho_eff, p_eff


def make_hubble_from_effective_density(
    h0_z2sigma: float,
    rho_eff_over_rho_crit0: FunctionOfA,
    omega_k_z2sigma: float = 0.0,
) -> Callable[[np.ndarray], np.ndarray]:
    """Build H_Z2Sigma(z) from active normalized rho_eff(a).

    The caller must provide active Z2/Sigma values. There are no Planck/LCDM
    defaults beyond the explicit curvature value supplied here.
    """

    if h0_z2sigma <= 0:
        raise ValueError("H0_Z2Sigma must be positive")

    def h_z2sigma(z):
        z_arr = np.asarray(z, dtype=float)
        if np.any(z_arr < 0):
            raise ValueError("Redshift must be non-negative")
        a = 1.0 / (1.0 + z_arr)
        rho_norm = np.asarray(rho_eff_over_rho_crit0(a), dtype=float)
        if rho_norm.shape != z_arr.shape:
            raise ValueError("rho_eff_over_rho_crit0(a) must match the input shape")
        e2 = rho_norm + omega_k_z2sigma / (a * a)
        if np.any(e2 <= 0):
            raise ValueError("H_Z2Sigma^2 must be positive on the requested grid")
        return h0_z2sigma * np.sqrt(e2)

    return h_z2sigma


def make_dimensionless_hubble_from_effective_density(
    rho_eff_over_rho_crit0: FunctionOfA,
    omega_k_z2sigma: float = 0.0,
) -> Callable[[np.ndarray], np.ndarray]:
    """Build E_Z2Sigma(z)=H_Z2Sigma(z)/H0 from active normalized density."""

    def e_z2sigma(z):
        z_arr = np.asarray(z, dtype=float)
        if np.any(z_arr < 0):
            raise ValueError("Redshift must be non-negative")
        a = 1.0 / (1.0 + z_arr)
        rho_norm = np.asarray(rho_eff_over_rho_crit0(a), dtype=float)
        if rho_norm.shape != z_arr.shape:
            raise ValueError("rho_eff_over_rho_crit0(a) must match the input shape")
        e2 = rho_norm + omega_k_z2sigma / (a * a)
        if np.any(e2 <= 0):
            raise ValueError("E_Z2Sigma^2 must be positive on the requested grid")
        return np.sqrt(e2)

    return e_z2sigma
