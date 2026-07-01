"""Weak-lensing spectra and real-space shear correlations.

This module supplies the technical bridge
``P_Weyl(k,z) -> P_kappa^ij(ell) -> xi_+/xi_-``.  The Weyl spectrum is an
input function so Janus/Holst physics can be injected explicitly without
fitting it inside the survey operator.
"""

from __future__ import annotations

from collections.abc import Callable

import numpy as np
from scipy.special import jv

from .lensing import (
    janus_open_angular_lensing_distance_kernel_mpc,
    janus_open_comoving_lensing_distance_kernel_mpc,
    janus_open_transverse_distance_mpc,
)
from .models import JanusExpansion


Array = np.ndarray
WeylPower = Callable[[Array, Array], Array]
ProjectionFactor = Callable[[Array], Array]


def normalized_source_distribution(z: Array, weights: Array) -> tuple[Array, Array]:
    z_values = np.asarray(z, dtype=float)
    source_weights = np.asarray(weights, dtype=float)
    if z_values.ndim != 1 or source_weights.ndim != 1 or z_values.shape != source_weights.shape:
        raise ValueError("z and weights must be matching one-dimensional arrays.")
    if np.any(z_values < 0.0) or np.any(source_weights < 0.0):
        raise ValueError("source distribution must be non-negative.")
    total = float(np.trapezoid(source_weights, z_values))
    if total <= 0.0:
        total = float(np.sum(source_weights))
    if total <= 0.0:
        raise ValueError("source distribution must have positive weight.")
    return z_values, source_weights / total


def source_bin_from_nz_rows(nz_rows: list[dict], bin_index: int) -> tuple[Array, Array]:
    z_key = f"Z_MID_BIN{bin_index}"
    z = np.asarray([float(row.get(z_key, row["Z_MID"])) for row in nz_rows], dtype=float)
    weights = np.asarray([float(row[f"BIN{bin_index}"]) for row in nz_rows], dtype=float)
    return normalized_source_distribution(z, weights)


def janus_lens_grid(
    z_max: float,
    *,
    q0: float = -0.087,
    h0: float = 70.0,
    samples: int = 256,
) -> tuple[JanusExpansion, Array, Array]:
    model = JanusExpansion.from_q0(q0)
    z_stop = min(float(z_max), model.z_max)
    if z_stop <= 0.0:
        raise ValueError("z_max must be positive.")
    z_lens = np.linspace(1.0e-4, z_stop, samples)
    chi = np.asarray(
        janus_open_transverse_distance_mpc(z_lens, model, h0),
        dtype=float,
    )
    return model, z_lens, chi


def janus_source_efficiency(
    z_lens: Array,
    source_z: Array,
    source_weights: Array,
    model: JanusExpansion,
    *,
    h0: float = 70.0,
    distance_kernel: str = "comoving",
) -> Array:
    z_sources, weights = normalized_source_distribution(source_z, source_weights)
    if distance_kernel not in {"comoving", "angular_lens"}:
        raise ValueError("distance_kernel must be 'comoving' or 'angular_lens'.")
    efficiency = np.zeros_like(z_lens, dtype=float)
    for z_source, weight in zip(z_sources, weights):
        if z_source <= 0.0 or z_source > model.z_max:
            continue
        kernel = (
            janus_open_comoving_lensing_distance_kernel_mpc
            if distance_kernel == "comoving"
            else janus_open_angular_lensing_distance_kernel_mpc
        )
        efficiency += weight * np.asarray(
            kernel(z_lens, float(z_source), model, h0),
            dtype=float,
        )
    return efficiency


def toy_weyl_power(
    k: Array,
    z: Array,
    *,
    amplitude: float = 1.0,
    spectral_index: float = 1.0,
    k_pivot: float = 0.2,
    k_cut: float = 8.0,
    growth_power: float = 1.0,
    mu_weyl: float = 1.0,
    slip: float = 1.0,
) -> Array:
    """Smooth non-fit Weyl spectrum scaffold with Janus/Holst modifier hooks."""

    k_values = np.asarray(k, dtype=float)
    z_values = np.asarray(z, dtype=float)
    if amplitude < 0.0 or k_pivot <= 0.0 or k_cut <= 0.0:
        raise ValueError("amplitude, k_pivot and k_cut must be valid positive scales.")
    safe_k = np.maximum(k_values, 1.0e-8)
    growth = (1.0 + z_values) ** (-growth_power)
    sigma_weyl = mu_weyl * (1.0 + slip) / 2.0
    return amplitude * sigma_weyl**2 * (safe_k / k_pivot) ** spectral_index * np.exp(
        -(safe_k / k_cut) ** 2
    ) * growth**2


def convergence_power_limber(
    ell: Array,
    z_lens: Array,
    chi_mpc: Array,
    efficiency_i: Array,
    efficiency_j: Array,
    weyl_power: WeylPower,
    projection_factor: ProjectionFactor | None = None,
) -> Array:
    ell_values = np.asarray(ell, dtype=float)
    z_values = np.asarray(z_lens, dtype=float)
    chi = np.asarray(chi_mpc, dtype=float)
    if np.any(ell_values <= 0.0) or np.any(chi <= 0.0):
        raise ValueError("ell and chi must be positive.")
    if not (z_values.shape == chi.shape == efficiency_i.shape == efficiency_j.shape):
        raise ValueError("z, chi and efficiency arrays must have the same shape.")
    k = ell_values[:, np.newaxis] / chi[np.newaxis, :]
    z_grid = np.broadcast_to(z_values[np.newaxis, :], k.shape)
    power = weyl_power(k, z_grid)
    projection = (
        np.ones_like(z_values, dtype=float)
        if projection_factor is None
        else np.asarray(projection_factor(z_values), dtype=float)
    )
    if projection.shape != z_values.shape or np.any(~np.isfinite(projection)):
        raise ValueError("projection_factor must return finite values on the lens grid.")
    integrand = (
        efficiency_i[np.newaxis, :]
        * efficiency_j[np.newaxis, :]
        / chi[np.newaxis, :] ** 2
        * power
        * projection[np.newaxis, :]
    )
    return np.trapezoid(integrand, chi, axis=1)


def xi_pm_from_pkappa(theta_rad: Array, ell: Array, pkappa: Array) -> tuple[Array, Array]:
    theta = np.asarray(theta_rad, dtype=float)
    ell_values = np.asarray(ell, dtype=float)
    power = np.asarray(pkappa, dtype=float)
    if theta.ndim != 1 or ell_values.ndim != 1 or power.shape != ell_values.shape:
        raise ValueError("theta, ell and pkappa must be matching one-dimensional inputs.")
    arg = theta[:, np.newaxis] * ell_values[np.newaxis, :]
    weight = ell_values[np.newaxis, :] * power[np.newaxis, :] / (2.0 * np.pi)
    xi_plus = np.trapezoid(weight * jv(0, arg), ell_values, axis=1)
    xi_minus = np.trapezoid(weight * jv(4, arg), ell_values, axis=1)
    return xi_plus, xi_minus


def arcmin_to_rad(theta_arcmin: Array) -> Array:
    return np.asarray(theta_arcmin, dtype=float) * np.pi / (180.0 * 60.0)


def janus_xi_curves_for_kids_bins(
    nz_rows: list[dict],
    theta_arcmin: Array,
    *,
    q0: float = -0.087,
    h0: float = 70.0,
    ell: Array | None = None,
    weyl_power: WeylPower | None = None,
    projection_factor: ProjectionFactor | None = None,
    distance_kernel: str = "comoving",
) -> tuple[dict[tuple[int, int], Array], dict[tuple[int, int], Array]]:
    theta = arcmin_to_rad(theta_arcmin)
    source_bins = {index: source_bin_from_nz_rows(nz_rows, index) for index in range(1, 6)}
    z_max = max(float(np.max(z)) for z, _ in source_bins.values())
    model, z_lens, chi = janus_lens_grid(z_max, q0=q0, h0=h0)
    ell_values = np.asarray(ell if ell is not None else np.geomspace(10.0, 1.0e4, 160), dtype=float)
    power_func = weyl_power or (lambda k, z: toy_weyl_power(k, z))
    efficiencies = {
        index: janus_source_efficiency(z_lens, z, weights, model, h0=h0, distance_kernel=distance_kernel)
        for index, (z, weights) in source_bins.items()
    }
    xi_plus: dict[tuple[int, int], Array] = {}
    xi_minus: dict[tuple[int, int], Array] = {}
    for i in range(1, 6):
        for j in range(i, 6):
            pkappa = convergence_power_limber(
                ell_values,
                z_lens,
                chi,
                efficiencies[i],
                efficiencies[j],
                power_func,
                projection_factor=projection_factor,
            )
            plus, minus = xi_pm_from_pkappa(theta, ell_values, pkappa)
            xi_plus[(i, j)] = plus
            xi_minus[(i, j)] = minus
    return xi_plus, xi_minus
