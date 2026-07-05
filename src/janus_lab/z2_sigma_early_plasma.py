"""Strict active Z2/Sigma early-plasma helpers."""

from __future__ import annotations

from typing import Callable

import numpy as np

from .constants import SPEED_OF_LIGHT_KM_S
from .physical_units import MPC_IN_METERS


FunctionOfZ = Callable[[np.ndarray], np.ndarray]


def make_conserved_baryon_density_z2sigma(rho_baryon0_z2sigma: float) -> FunctionOfZ:
    """Build active conserved baryon density history, rho_b(z)=rho_b0(1+z)^3."""

    if rho_baryon0_z2sigma <= 0.0:
        raise ValueError("rho_baryon0_z2sigma must be positive")

    def rho_baryon_z2sigma(z):
        z_arr = np.asarray(z, dtype=float)
        if np.any(z_arr < 0.0):
            raise ValueError("redshift must be non-negative")
        return float(rho_baryon0_z2sigma) * (1.0 + z_arr) ** 3

    return rho_baryon_z2sigma


def make_conserved_photon_density_z2sigma(rho_photon0_z2sigma: float) -> FunctionOfZ:
    """Build active conserved photon density history, rho_gamma(z)=rho_gamma0(1+z)^4."""

    if rho_photon0_z2sigma <= 0.0:
        raise ValueError("rho_photon0_z2sigma must be positive")

    def rho_photon_z2sigma(z):
        z_arr = np.asarray(z, dtype=float)
        if np.any(z_arr < 0.0):
            raise ValueError("redshift must be non-negative")
        return float(rho_photon0_z2sigma) * (1.0 + z_arr) ** 4

    return rho_photon_z2sigma


def make_conserved_photon_temperature_z2sigma(photon_temperature0_z2sigma: float) -> FunctionOfZ:
    """Build active photon temperature history, T_gamma(z)=T_gamma0(1+z)."""

    if photon_temperature0_z2sigma <= 0.0:
        raise ValueError("photon_temperature0_z2sigma must be positive")

    def photon_temperature_z2sigma(z):
        z_arr = np.asarray(z, dtype=float)
        if np.any(z_arr < 0.0):
            raise ValueError("redshift must be non-negative")
        return float(photon_temperature0_z2sigma) * (1.0 + z_arr)

    return photon_temperature_z2sigma


def make_free_electron_density_z2sigma(
    baryon_number_density_m3_z2sigma: FunctionOfZ,
    ionization_fraction_z2sigma: FunctionOfZ,
    *,
    electrons_per_baryon: float,
) -> FunctionOfZ:
    """Build active free-electron density n_e(z) from active baryon number and x_e."""

    if electrons_per_baryon <= 0.0:
        raise ValueError("electrons_per_baryon must be positive")

    def free_electron_density(z):
        z_arr = np.asarray(z, dtype=float)
        n_b = np.asarray(baryon_number_density_m3_z2sigma(z_arr), dtype=float)
        x_e = np.asarray(ionization_fraction_z2sigma(z_arr), dtype=float)
        if n_b.shape != z_arr.shape or x_e.shape != z_arr.shape:
            raise ValueError("baryon number density and ionization fraction must match the input shape")
        if np.any(n_b < 0.0) or np.any(x_e < 0.0):
            raise ValueError("baryon number density and ionization fraction must be non-negative")
        return float(electrons_per_baryon) * x_e * n_b

    return free_electron_density


def make_saha_ionization_fraction_z2sigma(
    baryon_number_density_m3_z2sigma: FunctionOfZ,
    photon_temperature_z2sigma: FunctionOfZ,
    *,
    electron_mass_kg: float,
    boltzmann_constant_j_k: float,
    hbar_j_s: float,
    hydrogen_ionization_energy_j: float,
) -> FunctionOfZ:
    """Build active hydrogen Saha-equilibrium ionization fraction x_e(z)."""

    if electron_mass_kg <= 0.0:
        raise ValueError("electron_mass_kg must be positive")
    if boltzmann_constant_j_k <= 0.0:
        raise ValueError("boltzmann_constant_j_k must be positive")
    if hbar_j_s <= 0.0:
        raise ValueError("hbar_j_s must be positive")
    if hydrogen_ionization_energy_j <= 0.0:
        raise ValueError("hydrogen_ionization_energy_j must be positive")

    def ionization_fraction(z):
        z_arr = np.asarray(z, dtype=float)
        if np.any(z_arr < 0.0):
            raise ValueError("redshift must be non-negative")
        n_b = np.asarray(baryon_number_density_m3_z2sigma(z_arr), dtype=float)
        temperature = np.asarray(photon_temperature_z2sigma(z_arr), dtype=float)
        if n_b.shape != z_arr.shape or temperature.shape != z_arr.shape:
            raise ValueError("baryon number density and photon temperature must match input shape")
        if np.any(n_b <= 0.0) or np.any(temperature <= 0.0):
            raise ValueError("baryon number density and photon temperature must be positive")
        thermal_prefactor = (
            electron_mass_kg
            * boltzmann_constant_j_k
            * temperature
            / (2.0 * np.pi * hbar_j_s**2)
        ) ** 1.5
        saha_ratio = (
            thermal_prefactor
            * np.exp(-hydrogen_ionization_energy_j / (boltzmann_constant_j_k * temperature))
            / n_b
        )
        values = 0.5 * (-saha_ratio + np.sqrt(saha_ratio**2 + 4.0 * saha_ratio))
        return np.clip(values, np.finfo(float).tiny, 1.0)

    return ionization_fraction


def make_baryon_mass_density_from_number_density_z2sigma(
    baryon_number_density_m3_z2sigma: FunctionOfZ,
    *,
    baryon_mass_kg: float,
) -> FunctionOfZ:
    """Build active baryon mass density from active baryon number density."""

    if baryon_mass_kg <= 0.0:
        raise ValueError("baryon_mass_kg must be positive")

    def baryon_mass_density(z):
        z_arr = np.asarray(z, dtype=float)
        n_b = np.asarray(baryon_number_density_m3_z2sigma(z_arr), dtype=float)
        if n_b.shape != z_arr.shape:
            raise ValueError("baryon number density must match the input shape")
        if np.any(n_b < 0.0):
            raise ValueError("baryon number density must be non-negative")
        return float(baryon_mass_kg) * n_b

    return baryon_mass_density


def make_baryon_number_density_from_mass_density_z2sigma(
    rho_baryon_mass_density_kg_m3_z2sigma: FunctionOfZ,
    *,
    baryon_mass_kg: float,
) -> FunctionOfZ:
    """Build active baryon number density from active baryon mass density."""

    if baryon_mass_kg <= 0.0:
        raise ValueError("baryon_mass_kg must be positive")

    def baryon_number_density(z):
        z_arr = np.asarray(z, dtype=float)
        rho_b = np.asarray(rho_baryon_mass_density_kg_m3_z2sigma(z_arr), dtype=float)
        if rho_b.shape != z_arr.shape:
            raise ValueError("rho_baryon_mass_density must match the input shape")
        if np.any(rho_b < 0.0):
            raise ValueError("rho_baryon_mass_density must be non-negative")
        return rho_b / float(baryon_mass_kg)

    return baryon_number_density


def make_blackbody_photon_energy_density_z2sigma(
    photon_temperature_z2sigma: FunctionOfZ,
    *,
    radiation_constant_j_m3_k4: float,
) -> FunctionOfZ:
    """Build active photon energy density from an active blackbody temperature."""

    if radiation_constant_j_m3_k4 <= 0.0:
        raise ValueError("radiation_constant_j_m3_k4 must be positive")

    def photon_energy_density(z):
        z_arr = np.asarray(z, dtype=float)
        temperature = np.asarray(photon_temperature_z2sigma(z_arr), dtype=float)
        if temperature.shape != z_arr.shape:
            raise ValueError("photon_temperature must match the input shape")
        if np.any(temperature <= 0.0):
            raise ValueError("photon_temperature must be positive")
        return float(radiation_constant_j_m3_k4) * temperature**4

    return photon_energy_density


def make_photon_baryon_sound_speed(
    rho_baryon_z2sigma: FunctionOfZ,
    rho_photon_z2sigma: FunctionOfZ,
) -> FunctionOfZ:
    """Build c_s^Z2Sigma(z) from supplied active baryon/photon densities."""

    def cs_z2sigma(z):
        z_arr = np.asarray(z, dtype=float)
        rho_b = np.asarray(rho_baryon_z2sigma(z_arr), dtype=float)
        rho_gamma = np.asarray(rho_photon_z2sigma(z_arr), dtype=float)
        if rho_b.shape != z_arr.shape or rho_gamma.shape != z_arr.shape:
            raise ValueError("rho_baryon and rho_photon must match the input shape")
        if np.any(rho_b < 0) or np.any(rho_gamma <= 0):
            raise ValueError("rho_baryon must be non-negative and rho_photon must be positive")
        loading = 3.0 * rho_b / (4.0 * rho_gamma)
        return SPEED_OF_LIGHT_KM_S / np.sqrt(3.0 * (1.0 + loading))

    return cs_z2sigma


def make_photon_baryon_sound_speed_over_c(
    rho_baryon_z2sigma: FunctionOfZ,
    rho_photon_z2sigma: FunctionOfZ,
) -> FunctionOfZ:
    """Build dimensionless c_s^Z2Sigma(z)/c from active baryon/photon densities."""

    cs_z2sigma = make_photon_baryon_sound_speed(rho_baryon_z2sigma, rho_photon_z2sigma)

    def cs_over_c_z2sigma(z):
        return cs_z2sigma(z) / SPEED_OF_LIGHT_KM_S

    return cs_over_c_z2sigma


def make_thomson_drag_rate_z2sigma(
    free_electron_density_m3_z2sigma: FunctionOfZ,
    rho_baryon_z2sigma: FunctionOfZ,
    rho_photon_z2sigma: FunctionOfZ,
    *,
    sigma_thomson_m2: float,
) -> FunctionOfZ:
    """Build Gamma_drag^Z2Sigma(z) in km/s/Mpc from active Thomson inputs.

    The rate uses the baryon momentum-loading factor
    R = 3 rho_b / (4 rho_gamma), so Gamma_drag = n_e sigma_T c / R.
    All densities and ionization histories are supplied by the active model.
    """

    if sigma_thomson_m2 <= 0.0:
        raise ValueError("sigma_thomson_m2 must be positive")

    def gamma_drag_z2sigma(z):
        z_arr = np.asarray(z, dtype=float)
        n_e = np.asarray(free_electron_density_m3_z2sigma(z_arr), dtype=float)
        rho_b = np.asarray(rho_baryon_z2sigma(z_arr), dtype=float)
        rho_gamma = np.asarray(rho_photon_z2sigma(z_arr), dtype=float)
        if n_e.shape != z_arr.shape or rho_b.shape != z_arr.shape or rho_gamma.shape != z_arr.shape:
            raise ValueError("n_e, rho_baryon and rho_photon must match the input shape")
        if np.any(n_e < 0.0) or np.any(rho_b <= 0.0) or np.any(rho_gamma <= 0.0):
            raise ValueError("n_e must be non-negative; rho_baryon and rho_photon must be positive")
        loading = 3.0 * rho_b / (4.0 * rho_gamma)
        if np.any(loading <= 0.0):
            raise ValueError("baryon loading must be positive")
        rate_s_inv = n_e * sigma_thomson_m2 * (SPEED_OF_LIGHT_KM_S * 1000.0) / loading
        return rate_s_inv * MPC_IN_METERS / 1000.0

    return gamma_drag_z2sigma


def find_drag_epoch_bracket_z2sigma(
    h_z2sigma: FunctionOfZ,
    gamma_drag_z2sigma: FunctionOfZ,
    z_grid,
) -> tuple[float, float]:
    """Find a grid bracket where Gamma_drag^Z2Sigma-H_Z2Sigma changes sign."""

    grid = np.asarray(z_grid, dtype=float)
    if grid.ndim != 1 or len(grid) < 2:
        raise ValueError("z_grid must be one-dimensional with at least two points")
    if np.any(grid <= 0.0) or np.any(np.diff(grid) <= 0.0):
        raise ValueError("z_grid must be positive and strictly increasing")

    h_values = np.asarray(h_z2sigma(grid), dtype=float)
    gamma_values = np.asarray(gamma_drag_z2sigma(grid), dtype=float)
    if h_values.shape != grid.shape or gamma_values.shape != grid.shape:
        raise ValueError("H_Z2Sigma and Gamma_drag must match z_grid shape")
    if np.any(h_values <= 0.0) or np.any(gamma_values <= 0.0):
        raise ValueError("H_Z2Sigma and Gamma_drag must be positive on z_grid")
    residual = gamma_values - h_values
    if np.any(residual == 0.0):
        index = int(np.where(residual == 0.0)[0][0])
        if index == 0:
            return float(grid[0]), float(grid[1])
        return float(grid[index - 1]), float(grid[index])
    signs = np.sign(residual)
    crossing = np.where(signs[:-1] * signs[1:] < 0.0)[0]
    if len(crossing) == 0:
        raise ValueError("z_grid does not bracket Gamma_drag-H=0")
    index = int(crossing[0])
    return float(grid[index]), float(grid[index + 1])


def solve_drag_epoch_z2sigma(
    h_z2sigma: FunctionOfZ,
    gamma_drag_z2sigma: FunctionOfZ,
    z_low: float,
    z_high: float,
    iterations: int = 96,
) -> float:
    """Solve Gamma_drag^Z2Sigma(z_d) = H_Z2Sigma(z_d) by bisection."""

    if z_low <= 0 or z_high <= z_low:
        raise ValueError("Require 0 < z_low < z_high")
    if iterations < 8:
        raise ValueError("iterations must be >= 8")

    def residual(z_value: float) -> float:
        z = np.asarray([z_value], dtype=float)
        h = float(np.asarray(h_z2sigma(z), dtype=float)[0])
        gamma = float(np.asarray(gamma_drag_z2sigma(z), dtype=float)[0])
        if h <= 0 or gamma <= 0:
            raise ValueError("H_Z2Sigma and Gamma_drag must be positive")
        return gamma - h

    lo = float(z_low)
    hi = float(z_high)
    f_lo = residual(lo)
    f_hi = residual(hi)
    if f_lo == 0.0:
        return lo
    if f_hi == 0.0:
        return hi
    if f_lo * f_hi > 0.0:
        raise ValueError("Drag epoch bracket must straddle Gamma_drag-H=0")

    for _ in range(iterations):
        mid = 0.5 * (lo + hi)
        f_mid = residual(mid)
        if f_mid == 0.0:
            return mid
        if f_lo * f_mid < 0.0:
            hi = mid
            f_hi = f_mid
        else:
            lo = mid
            f_lo = f_mid
    return 0.5 * (lo + hi)


def make_drag_rate_over_h0_z2sigma(
    gamma_drag_z2sigma: FunctionOfZ,
    h0_z2sigma_km_s_mpc: float,
) -> FunctionOfZ:
    """Build dimensionless Gamma_drag^Z2Sigma/H0 from active dimensional rates."""

    if h0_z2sigma_km_s_mpc <= 0.0:
        raise ValueError("h0_z2sigma_km_s_mpc must be positive")

    def gamma_over_h0(z):
        z_arr = np.asarray(z, dtype=float)
        gamma = np.asarray(gamma_drag_z2sigma(z_arr), dtype=float)
        if gamma.shape != z_arr.shape:
            raise ValueError("Gamma_drag must match the input shape")
        if np.any(gamma <= 0.0):
            raise ValueError("Gamma_drag must be positive")
        return gamma / float(h0_z2sigma_km_s_mpc)

    return gamma_over_h0
