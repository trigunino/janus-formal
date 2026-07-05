"""Matter-flux component builders for the active Z2/Sigma BAO path."""

from __future__ import annotations

from collections.abc import Callable

import numpy as np

from .z2_sigma_flrw_component_manifest import FORBIDDEN_PROVENANCE_TOKENS


ArrayFn = Callable[[np.ndarray], np.ndarray]


def _clean_source(source: str, field: str) -> str:
    cleaned = str(source).strip()
    if not cleaned:
        raise ValueError(f"Missing active provenance for {field}")
    lowered = cleaned.lower()
    if any(token in lowered for token in FORBIDDEN_PROVENANCE_TOKENS):
        raise ValueError(f"Forbidden provenance for {field}: {cleaned}")
    return cleaned


def make_transparent_matter_flux_components(
    *,
    active_sigma_transparency_derived: bool,
) -> tuple[ArrayFn, ArrayFn]:
    """Return zero matter-flux rho/p only after active transparency is derived."""

    if not active_sigma_transparency_derived:
        raise ValueError("active Sigma transparency must be derived before setting matter_flux=0")

    def zero(a: np.ndarray) -> np.ndarray:
        grid = np.asarray(a, dtype=float)
        return np.zeros_like(grid)

    return zero, zero


def build_transparent_matter_flux_component_payload(
    *,
    a_grid: list[float] | np.ndarray,
    active_sigma_transparency_derived: bool,
    transparency_provenance: str,
) -> dict:
    """Build matter-flux component arrays only from an active transparency proof."""

    grid = np.asarray(a_grid, dtype=float)
    if grid.ndim != 1 or len(grid) < 2:
        raise ValueError("a_grid must be one-dimensional with at least two points")
    if np.any(grid <= 0.0) or np.any(np.diff(grid) <= 0.0):
        raise ValueError("a_grid must be positive and strictly increasing")
    provenance = _clean_source(transparency_provenance, "matter_flux_transparency")
    rho, pressure = make_transparent_matter_flux_components(
        active_sigma_transparency_derived=active_sigma_transparency_derived
    )
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "component_route": "transparent_sigma_zero_flux",
        "active_sigma_transparency_derived": True,
        "a_grid": grid.tolist(),
        "flrw_components_over_rho_crit0": {
            "matter_flux_rho": rho(grid).tolist(),
            "matter_flux_p": pressure(grid).tolist(),
        },
        "component_provenance": {
            "matter_flux_rho": provenance,
            "matter_flux_p": provenance,
        },
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_reuse_used": False,
        "phenomenological_holst_bao_scan_used": False,
    }


def project_active_matter_flux_radial_values(
    *,
    a_grid: list[float] | np.ndarray,
    T_plus_munu_values: list | np.ndarray,
    T_minus_munu_values: list | np.ndarray,
    tangent_vectors_values: list | np.ndarray,
    normal_plus_values: list | np.ndarray,
    normal_minus_values: list | np.ndarray,
    radial_variation_tangent_weights: list | np.ndarray,
    eps_Z2: float = -1.0,
) -> dict:
    """Project active plus/minus stresses onto Sigma and reduce along delta R."""

    grid = np.asarray(a_grid, dtype=float)
    if grid.ndim != 1 or len(grid) < 2:
        raise ValueError("a_grid must be one-dimensional with at least two points")
    if np.any(grid <= 0.0) or np.any(np.diff(grid) <= 0.0):
        raise ValueError("a_grid must be positive and strictly increasing")

    T_plus = np.asarray(T_plus_munu_values, dtype=float)
    T_minus = np.asarray(T_minus_munu_values, dtype=float)
    tangents = np.asarray(tangent_vectors_values, dtype=float)
    normal_plus = np.asarray(normal_plus_values, dtype=float)
    normal_minus = np.asarray(normal_minus_values, dtype=float)
    radial_weights = np.asarray(radial_variation_tangent_weights, dtype=float)
    eps_z2 = float(eps_Z2)

    n_grid = len(grid)
    if T_plus.shape != T_minus.shape or T_plus.ndim != 3 or T_plus.shape[0] != n_grid:
        raise ValueError("T_plus/minus must have shape [len(a_grid), dim, dim]")
    dim = T_plus.shape[1]
    if T_plus.shape[2] != dim:
        raise ValueError("T_plus/minus tensors must be square")
    if tangents.ndim != 3 or tangents.shape[0] != n_grid or tangents.shape[2] != dim:
        raise ValueError("tangent_vectors_values must have shape [len(a_grid), n_tangent, dim]")
    n_tangent = tangents.shape[1]
    if normal_plus.shape != (n_grid, dim) or normal_minus.shape != (n_grid, dim):
        raise ValueError("normal_plus/minus_values must have shape [len(a_grid), dim]")
    if radial_weights.shape != (n_grid, n_tangent):
        raise ValueError("radial_variation_tangent_weights must have shape [len(a_grid), n_tangent]")
    for array_name, array in [
        ("T_plus_munu_values", T_plus),
        ("T_minus_munu_values", T_minus),
        ("tangent_vectors_values", tangents),
        ("normal_plus_values", normal_plus),
        ("normal_minus_values", normal_minus),
        ("radial_variation_tangent_weights", radial_weights),
    ]:
        if not np.all(np.isfinite(array)):
            raise ValueError(f"{array_name} must be finite")

    flux_plus = np.einsum("gmn,gam,gn->ga", T_plus, tangents, normal_plus)
    flux_minus = np.einsum("gmn,gam,gn->ga", T_minus, tangents, normal_minus)
    net_flux = flux_plus + eps_z2 * flux_minus
    radial_values = np.einsum("ga,ga->g", net_flux, radial_weights)
    return {
        "a_grid": grid.tolist(),
        "F_plus_tangent_values": flux_plus.tolist(),
        "F_minus_tangent_values": flux_minus.tolist(),
        "F_Z2Sigma_tangent_values": net_flux.tolist(),
        "E_matterFlux_values": radial_values.tolist(),
        "eps_Z2": eps_z2,
    }


def build_active_matter_flux_projection_payload(source: dict) -> dict:
    """Build the strict active-projection radial matter-flux payload."""

    projection = project_active_matter_flux_radial_values(
        a_grid=source["a_grid"],
        T_plus_munu_values=source["T_plus_munu_values"],
        T_minus_munu_values=source["T_minus_munu_values"],
        tangent_vectors_values=source["tangent_vectors_values"],
        normal_plus_values=source["normal_plus_values"],
        normal_minus_values=source["normal_minus_values"],
        radial_variation_tangent_weights=source["radial_variation_tangent_weights"],
        eps_Z2=float(source.get("eps_Z2", -1.0)),
    )
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_reuse_used": False,
        "archived_z4_background_reuse_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "observational_H0_fit_used": False,
        "observational_curvature_fit_used": False,
        "active_flux_projection_ready": True,
        "matter_flux_radial_reduction_ready": True,
        "selected_route": "active_projection",
        "projection_formula": "F_a^Z2Sigma = T_plus_munu e_a^mu n_plus^nu + eps_Z2 T_minus_munu e_a^mu n_minus^nu",
        "radial_reduction_formula": "E_matterFlux = F_a^Z2Sigma deltaX_RSigma^a",
        **projection,
    }


def perfect_fluid_stress_covariant_grid(
    *,
    rho_values: list[float] | np.ndarray,
    pressure_values: list[float] | np.ndarray,
    metric_covariant_values: list | np.ndarray,
    four_velocity_contravariant_values: list | np.ndarray,
) -> list:
    """Return T_mn=(rho+p)u_m u_n+p g_mn on an active grid."""

    rho = np.asarray(rho_values, dtype=float)
    pressure = np.asarray(pressure_values, dtype=float)
    metric = np.asarray(metric_covariant_values, dtype=float)
    velocity = np.asarray(four_velocity_contravariant_values, dtype=float)
    if rho.ndim != 1 or pressure.shape != rho.shape:
        raise ValueError("rho_values and pressure_values must be aligned one-dimensional arrays")
    if metric.ndim != 3 or metric.shape[0] != len(rho) or metric.shape[1] != metric.shape[2]:
        raise ValueError("metric_covariant_values must have shape [n_grid, dim, dim]")
    dim = metric.shape[1]
    if velocity.shape != (len(rho), dim):
        raise ValueError("four_velocity_contravariant_values must have shape [n_grid, dim]")
    for name, array in [
        ("rho_values", rho),
        ("pressure_values", pressure),
        ("metric_covariant_values", metric),
        ("four_velocity_contravariant_values", velocity),
    ]:
        if not np.all(np.isfinite(array)):
            raise ValueError(f"{name} must be finite")
    for item in metric:
        if not np.allclose(item, item.T):
            raise ValueError("metric_covariant_values must be symmetric")
    u_cov = np.einsum("gmn,gn->gm", metric, velocity)
    stress = (rho + pressure)[:, None, None] * np.einsum("gm,gn->gmn", u_cov, u_cov)
    stress = stress + pressure[:, None, None] * metric
    return stress.tolist()


def build_bulk_stress_on_sigma_payload(source: dict) -> dict:
    """Build active plus/minus covariant stress tensors on Sigma."""

    T_plus = perfect_fluid_stress_covariant_grid(
        rho_values=source["rho_plus_values"],
        pressure_values=source["p_plus_values"],
        metric_covariant_values=source["metric_plus_munu_values"],
        four_velocity_contravariant_values=source["u_plus_contravariant_values"],
    )
    T_minus = perfect_fluid_stress_covariant_grid(
        rho_values=source["rho_minus_values"],
        pressure_values=source["p_minus_values"],
        metric_covariant_values=source["metric_minus_munu_values"],
        four_velocity_contravariant_values=source["u_minus_contravariant_values"],
    )
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_reuse_used": False,
        "archived_z4_background_reuse_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "observational_H0_fit_used": False,
        "observational_curvature_fit_used": False,
        "bulk_stress_model": "perfect_fluid_covariant",
        "a_grid": list(source["a_grid"]),
        "T_plus_munu_values": T_plus,
        "T_minus_munu_values": T_minus,
        "stress_formula": "T_munu=(rho+p)u_mu u_nu+p g_munu",
        "bulk_stress_on_sigma_ready": True,
    }
