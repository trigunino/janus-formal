"""Strict writer for active Z2/Sigma BAO component manifests."""

from __future__ import annotations

import json
from collections.abc import Callable
from dataclasses import dataclass
from pathlib import Path

import numpy as np

from .z2_sigma_bao_schema import FORBIDDEN_PROVENANCE_TOKENS, REQUIRED_COMPONENT_PROVENANCE
from .z2_sigma_background_manifest import (
    load_active_z2sigma_background_scalar_manifest,
    validate_active_z2sigma_scalar_provenance,
)
from .z2_sigma_early_plasma_manifest import (
    EARLY_PLASMA_FIELDS,
    load_active_z2sigma_early_plasma_manifest,
)
from .z2_sigma_flrw_component_manifest import load_active_z2sigma_flrw_component_manifest
from .z2_sigma_normalization import make_active_z2sigma_critical_normalization


ArrayFn = Callable[[np.ndarray], np.ndarray]


@dataclass(frozen=True)
class Z2SigmaBAOComponentFunctions:
    cartan_ghy_rho: ArrayFn
    cartan_ghy_p: ArrayFn
    holst_nieh_yan_rho: ArrayFn
    holst_nieh_yan_p: ArrayFn
    matter_flux_rho: ArrayFn
    matter_flux_p: ArrayFn
    counterterm_rho: ArrayFn
    counterterm_p: ArrayFn
    rho_baryon_z2sigma: ArrayFn
    rho_photon_z2sigma: ArrayFn
    gamma_drag_z2sigma: ArrayFn


@dataclass(frozen=True)
class Z2SigmaFLRWComponentFunctions:
    cartan_ghy_rho: ArrayFn
    cartan_ghy_p: ArrayFn
    holst_nieh_yan_rho: ArrayFn
    holst_nieh_yan_p: ArrayFn
    matter_flux_rho: ArrayFn
    matter_flux_p: ArrayFn
    counterterm_rho: ArrayFn
    counterterm_p: ArrayFn


def _evaluate_on_grid(function: ArrayFn, grid: np.ndarray, name: str) -> list[float]:
    values = np.asarray(function(grid), dtype=float)
    if values.shape != grid.shape:
        raise ValueError(f"{name} returned shape {values.shape}, expected {grid.shape}")
    if not np.all(np.isfinite(values)):
        raise ValueError(f"{name} returned non-finite values")
    return [float(value) for value in values]


def _validate_grid(grid, name: str, *, positive: bool) -> np.ndarray:
    values = np.asarray(grid, dtype=float)
    if values.ndim != 1 or len(values) < 2:
        raise ValueError(f"{name} must be a one-dimensional grid with at least two points")
    if np.any(np.diff(values) <= 0):
        raise ValueError(f"{name} must be strictly increasing")
    if positive and np.any(values <= 0):
        raise ValueError(f"{name} must be positive")
    if not positive and np.any(values < 0):
        raise ValueError(f"{name} must be non-negative")
    return values


def _validate_provenance(component_provenance: dict[str, str]) -> dict[str, str]:
    cleaned: dict[str, str] = {}
    for field in REQUIRED_COMPONENT_PROVENANCE:
        source = str(component_provenance.get(field, "")).strip()
        if not source:
            raise ValueError(f"Missing component provenance for {field}")
        lowered = source.lower()
        if any(token in lowered for token in FORBIDDEN_PROVENANCE_TOKENS):
            raise ValueError(f"Forbidden component provenance for {field}: {source}")
        cleaned[field] = source
    return cleaned


def _validate_flrw_provenance(component_provenance: dict[str, str]) -> dict[str, str]:
    cleaned: dict[str, str] = {}
    for field in REQUIRED_COMPONENT_PROVENANCE:
        if field in EARLY_PLASMA_FIELDS:
            continue
        source = str(component_provenance.get(field, "")).strip()
        if not source:
            raise ValueError(f"Missing component provenance for {field}")
        lowered = source.lower()
        if any(token in lowered for token in FORBIDDEN_PROVENANCE_TOKENS):
            raise ValueError(f"Forbidden component provenance for {field}: {source}")
        cleaned[field] = source
    return cleaned


def write_active_z2sigma_bao_component_manifest(
    path: Path,
    *,
    a_grid,
    z_grid,
    h0_z2sigma_km_s_mpc: float,
    omega_k_z2sigma: float,
    z_d_bracket: tuple[float, float] | None,
    z_max: float,
    components: Z2SigmaBAOComponentFunctions,
    component_provenance: dict[str, str],
    scalar_provenance: dict[str, str],
    gravitational_constant_si_z2sigma: float | None = None,
) -> Path:
    """Write `bao_component_inputs.json` from active-derived functions only."""

    if h0_z2sigma_km_s_mpc <= 0.0:
        raise ValueError("h0_z2sigma_km_s_mpc must be positive")
    if z_d_bracket is not None:
        z_low, z_high = [float(value) for value in z_d_bracket]
        if not (0.0 <= z_low < z_high <= z_max):
            raise ValueError("z_d_bracket must satisfy 0 <= low < high <= z_max")
        z_d_bracket_payload: list[float] | None = [z_low, z_high]
    else:
        z_d_bracket_payload = None

    a_values = _validate_grid(a_grid, "a_grid", positive=True)
    z_values = _validate_grid(z_grid, "z_grid", positive=False)
    provenance = _validate_provenance(component_provenance)
    scalar_sources = validate_active_z2sigma_scalar_provenance(scalar_provenance)
    normalization_kwargs = {}
    if gravitational_constant_si_z2sigma is not None:
        normalization_kwargs["gravitational_constant_si_z2sigma"] = gravitational_constant_si_z2sigma
    normalization = make_active_z2sigma_critical_normalization(
        h0_z2sigma_km_s_mpc,
        **normalization_kwargs,
    )

    flrw = {
        "cartan_ghy_rho": _evaluate_on_grid(components.cartan_ghy_rho, a_values, "cartan_ghy_rho"),
        "cartan_ghy_p": _evaluate_on_grid(components.cartan_ghy_p, a_values, "cartan_ghy_p"),
        "holst_nieh_yan_rho": _evaluate_on_grid(components.holst_nieh_yan_rho, a_values, "holst_nieh_yan_rho"),
        "holst_nieh_yan_p": _evaluate_on_grid(components.holst_nieh_yan_p, a_values, "holst_nieh_yan_p"),
        "matter_flux_rho": _evaluate_on_grid(components.matter_flux_rho, a_values, "matter_flux_rho"),
        "matter_flux_p": _evaluate_on_grid(components.matter_flux_p, a_values, "matter_flux_p"),
        "counterterm_rho": _evaluate_on_grid(components.counterterm_rho, a_values, "counterterm_rho"),
        "counterterm_p": _evaluate_on_grid(components.counterterm_p, a_values, "counterterm_p"),
    }
    early = {
        "rho_baryon_Z2Sigma": _evaluate_on_grid(
            components.rho_baryon_z2sigma, z_values, "rho_baryon_Z2Sigma"
        ),
        "rho_photon_Z2Sigma": _evaluate_on_grid(
            components.rho_photon_z2sigma, z_values, "rho_photon_Z2Sigma"
        ),
        "Gamma_drag_Z2Sigma": _evaluate_on_grid(
            components.gamma_drag_z2sigma, z_values, "Gamma_drag_Z2Sigma"
        ),
    }

    payload = {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_rd_used": False,
        "archived_z4_reuse_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "H0_Z2Sigma_km_s_Mpc": float(h0_z2sigma_km_s_mpc),
        "omega_k_Z2Sigma": float(omega_k_z2sigma),
        "critical_normalization": {
            "rho_crit0_Z2Sigma_kg_m3": normalization.rho_crit0_kg_m3,
            "kappa_Z2Sigma_SI": normalization.kappa_si,
            "kappa_rho_crit0_Z2Sigma_SI": normalization.kappa_rho_crit0_si,
            "gravitational_constant_source": scalar_sources["G_Z2Sigma"],
        },
        "a_grid": [float(value) for value in a_values],
        "z_grid": [float(value) for value in z_values],
        "z_d_bracket": z_d_bracket_payload,
        "z_max": float(z_max),
        "flrw_components_over_rho_crit0": flrw,
        "early_plasma": early,
        "component_provenance": provenance,
        "scalar_provenance": scalar_sources,
    }
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    return path


def write_active_z2sigma_bao_component_manifest_from_flrw_and_early_plasma_manifest(
    path: Path,
    *,
    a_grid,
    h0_z2sigma_km_s_mpc: float,
    omega_k_z2sigma: float,
    z_max: float,
    flrw_components: Z2SigmaFLRWComponentFunctions,
    flrw_component_provenance: dict[str, str],
    scalar_provenance: dict[str, str],
    early_plasma_manifest_path: Path,
    gravitational_constant_si_z2sigma: float | None = None,
) -> Path:
    """Write a full BAO component manifest from FLRW components plus early-plasma manifest."""

    if h0_z2sigma_km_s_mpc <= 0.0:
        raise ValueError("h0_z2sigma_km_s_mpc must be positive")
    a_values = _validate_grid(a_grid, "a_grid", positive=True)
    early_payload = load_active_z2sigma_early_plasma_manifest(early_plasma_manifest_path)
    z_values = _validate_grid(early_payload["z_grid"], "z_grid", positive=False)
    z_d_bracket = early_payload.get("z_d_bracket")
    if z_d_bracket is not None:
        z_low, z_high = [float(value) for value in z_d_bracket]
        if not (0.0 <= z_low < z_high <= z_max):
            raise ValueError("z_d_bracket must satisfy 0 <= low < high <= z_max")
        z_d_bracket_payload: list[float] | None = [z_low, z_high]
    else:
        z_d_bracket_payload = None

    flrw_provenance = _validate_flrw_provenance(flrw_component_provenance)
    scalar_sources = validate_active_z2sigma_scalar_provenance(scalar_provenance)
    component_provenance = {
        **flrw_provenance,
        **{field: early_payload["component_provenance"][field] for field in EARLY_PLASMA_FIELDS},
    }
    provenance = _validate_provenance(component_provenance)
    normalization_kwargs = {}
    if gravitational_constant_si_z2sigma is not None:
        normalization_kwargs["gravitational_constant_si_z2sigma"] = gravitational_constant_si_z2sigma
    normalization = make_active_z2sigma_critical_normalization(
        h0_z2sigma_km_s_mpc,
        **normalization_kwargs,
    )

    payload = {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_rd_used": False,
        "archived_z4_reuse_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "H0_Z2Sigma_km_s_Mpc": float(h0_z2sigma_km_s_mpc),
        "omega_k_Z2Sigma": float(omega_k_z2sigma),
        "critical_normalization": {
            "rho_crit0_Z2Sigma_kg_m3": normalization.rho_crit0_kg_m3,
            "kappa_Z2Sigma_SI": normalization.kappa_si,
            "kappa_rho_crit0_Z2Sigma_SI": normalization.kappa_rho_crit0_si,
            "gravitational_constant_source": scalar_sources["G_Z2Sigma"],
        },
        "a_grid": [float(value) for value in a_values],
        "z_grid": [float(value) for value in z_values],
        "z_d_bracket": z_d_bracket_payload,
        "z_max": float(z_max),
        "flrw_components_over_rho_crit0": {
            "cartan_ghy_rho": _evaluate_on_grid(flrw_components.cartan_ghy_rho, a_values, "cartan_ghy_rho"),
            "cartan_ghy_p": _evaluate_on_grid(flrw_components.cartan_ghy_p, a_values, "cartan_ghy_p"),
            "holst_nieh_yan_rho": _evaluate_on_grid(flrw_components.holst_nieh_yan_rho, a_values, "holst_nieh_yan_rho"),
            "holst_nieh_yan_p": _evaluate_on_grid(flrw_components.holst_nieh_yan_p, a_values, "holst_nieh_yan_p"),
            "matter_flux_rho": _evaluate_on_grid(flrw_components.matter_flux_rho, a_values, "matter_flux_rho"),
            "matter_flux_p": _evaluate_on_grid(flrw_components.matter_flux_p, a_values, "matter_flux_p"),
            "counterterm_rho": _evaluate_on_grid(flrw_components.counterterm_rho, a_values, "counterterm_rho"),
            "counterterm_p": _evaluate_on_grid(flrw_components.counterterm_p, a_values, "counterterm_p"),
        },
        "early_plasma": early_payload["early_plasma"],
        "component_provenance": provenance,
        "scalar_provenance": scalar_sources,
    }
    destination = Path(path)
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    return destination


def write_active_z2sigma_bao_component_manifest_from_background_flrw_and_early_plasma_manifest(
    path: Path,
    *,
    background_scalar_manifest_path: Path,
    a_grid,
    z_max: float,
    flrw_components: Z2SigmaFLRWComponentFunctions,
    flrw_component_provenance: dict[str, str],
    early_plasma_manifest_path: Path,
) -> Path:
    background = load_active_z2sigma_background_scalar_manifest(background_scalar_manifest_path)
    destination = write_active_z2sigma_bao_component_manifest_from_flrw_and_early_plasma_manifest(
        path,
        a_grid=a_grid,
        h0_z2sigma_km_s_mpc=float(background["H0_Z2Sigma_km_s_Mpc"]),
        omega_k_z2sigma=float(background["omega_k_Z2Sigma"]),
        z_max=z_max,
        flrw_components=flrw_components,
        flrw_component_provenance=flrw_component_provenance,
        scalar_provenance=background["scalar_provenance"],
        early_plasma_manifest_path=early_plasma_manifest_path,
        gravitational_constant_si_z2sigma=float(background["gravitational_constant_si_Z2Sigma"]),
    )
    return destination


def write_active_z2sigma_bao_component_manifest_from_background_flrw_component_and_early_plasma_manifests(
    path: Path,
    *,
    background_scalar_manifest_path: Path,
    flrw_component_manifest_path: Path,
    early_plasma_manifest_path: Path,
    z_max: float,
) -> Path:
    """Write a BAO component manifest from three strict active manifests."""

    background = load_active_z2sigma_background_scalar_manifest(background_scalar_manifest_path)
    flrw_payload = load_active_z2sigma_flrw_component_manifest(flrw_component_manifest_path)
    early_payload = load_active_z2sigma_early_plasma_manifest(early_plasma_manifest_path)
    scalar_sources = validate_active_z2sigma_scalar_provenance(background["scalar_provenance"])
    z_values = _validate_grid(early_payload["z_grid"], "z_grid", positive=False)
    z_d_bracket = early_payload.get("z_d_bracket")
    if z_d_bracket is not None:
        z_low, z_high = [float(value) for value in z_d_bracket]
        if not (0.0 <= z_low < z_high <= z_max):
            raise ValueError("z_d_bracket must satisfy 0 <= low < high <= z_max")
        z_d_bracket_payload: list[float] | None = [z_low, z_high]
    else:
        z_d_bracket_payload = None
    component_provenance = {
        **flrw_payload["component_provenance"],
        **{field: early_payload["component_provenance"][field] for field in EARLY_PLASMA_FIELDS},
    }
    provenance = _validate_provenance(component_provenance)
    normalization = background["critical_normalization"]
    payload = {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_rd_used": False,
        "archived_z4_reuse_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "H0_Z2Sigma_km_s_Mpc": float(background["H0_Z2Sigma_km_s_Mpc"]),
        "omega_k_Z2Sigma": float(background["omega_k_Z2Sigma"]),
        "critical_normalization": {
            "rho_crit0_Z2Sigma_kg_m3": float(normalization["rho_crit0_Z2Sigma_kg_m3"]),
            "kappa_Z2Sigma_SI": float(normalization["kappa_Z2Sigma_SI"]),
            "kappa_rho_crit0_Z2Sigma_SI": float(normalization["kappa_rho_crit0_Z2Sigma_SI"]),
            "gravitational_constant_source": scalar_sources["G_Z2Sigma"],
        },
        "a_grid": [float(value) for value in flrw_payload["a_grid"]],
        "z_grid": [float(value) for value in z_values],
        "z_d_bracket": z_d_bracket_payload,
        "z_max": float(z_max),
        "flrw_components_over_rho_crit0": flrw_payload["flrw_components_over_rho_crit0"],
        "early_plasma": early_payload["early_plasma"],
        "component_provenance": provenance,
        "scalar_provenance": scalar_sources,
    }
    destination = Path(path)
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    return destination
