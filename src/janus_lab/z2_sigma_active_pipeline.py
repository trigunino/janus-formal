"""Build official ActiveZ2Sigma BAO inputs from derived component manifests."""

from __future__ import annotations

import json
import hashlib
from pathlib import Path

import numpy as np

from .z2_sigma_background_manifest import validate_active_z2sigma_scalar_provenance
from .z2_sigma_background_inputs import build_active_z2sigma_background_scalar_payload
from .z2_sigma_early_plasma_manifest import load_active_z2sigma_early_plasma_manifest
from .z2_sigma_flrw_component_manifest import load_active_z2sigma_flrw_component_manifest
from .z2_sigma_active_inputs import (
    load_active_z2sigma_scale_free_background_primitive_inputs,
    load_active_z2sigma_scale_free_plasma_primitive_inputs,
    load_active_z2sigma_scale_free_primitive_inputs,
    write_active_z2sigma_bao_manifest,
    write_active_z2sigma_scale_free_background_primitive_manifest,
    write_active_z2sigma_scale_free_bao_manifest,
    write_active_z2sigma_scale_free_plasma_primitive_manifest,
    write_active_z2sigma_scale_free_primitive_manifest,
)
from .z2_sigma_background import (
    EffectiveFluidComponents,
    make_effective_fluid_functions,
    make_dimensionless_hubble_from_effective_density,
    make_hubble_from_effective_density,
)
from .z2_sigma_early_plasma import (
    find_drag_epoch_bracket_z2sigma,
    make_drag_rate_over_h0_z2sigma,
    make_photon_baryon_sound_speed,
    make_photon_baryon_sound_speed_over_c,
    solve_drag_epoch_z2sigma,
)
from .z2_sigma_bao_schema import (
    FORBIDDEN_FLAGS,
    FORBIDDEN_PROVENANCE_TOKENS,
    REQUIRED_COMPONENT_PROVENANCE,
)


def _require_active_payload(path: Path) -> dict:
    payload = json.loads(Path(path).read_text(encoding="utf-8"))
    if payload.get("active_core") != "Z2_tunnel_Sigma":
        raise ValueError("Component manifest active_core must be Z2_tunnel_Sigma")
    if payload.get("source") != "active_derived":
        raise ValueError("Component manifest source must be active_derived")
    for key in FORBIDDEN_FLAGS:
        if payload.get(key) is not False:
            raise ValueError(f"Forbidden provenance flag must be false: {key}")
    provenance = payload.get("component_provenance")
    if not isinstance(provenance, dict):
        raise ValueError("component_provenance is required")
    for field in REQUIRED_COMPONENT_PROVENANCE:
        source = str(provenance.get(field, "")).lower()
        if not source:
            raise ValueError(f"Missing component provenance for {field}")
        if any(token in source for token in FORBIDDEN_PROVENANCE_TOKENS):
            raise ValueError(f"Forbidden component provenance for {field}: {source}")
    validate_active_z2sigma_scalar_provenance(payload.get("scalar_provenance", {}))
    return payload


def _grid_function(x_grid: np.ndarray, y_values: np.ndarray):
    if x_grid.ndim != 1 or y_values.shape != x_grid.shape:
        raise ValueError("Grid functions must be one-dimensional and aligned")
    if np.any(np.diff(x_grid) <= 0):
        raise ValueError("Grid must be strictly increasing")

    def function(x):
        return np.interp(np.asarray(x, dtype=float), x_grid, y_values)

    return function


def write_bao_manifest_from_active_component_manifest(
    component_manifest_path: Path,
    output_manifest_path: Path,
) -> Path:
    """Create official BAO inputs from active component arrays."""

    payload = _require_active_payload(component_manifest_path)
    a_grid = np.asarray(payload["a_grid"], dtype=float)
    z_grid = np.asarray(payload["z_grid"], dtype=float)
    if np.any(a_grid <= 0) or np.any(np.diff(a_grid) <= 0):
        raise ValueError("a_grid must be positive and strictly increasing")
    if np.any(z_grid < 0) or np.any(np.diff(z_grid) <= 0):
        raise ValueError("z_grid must be non-negative and strictly increasing")

    components_payload = payload["flrw_components_over_rho_crit0"]
    components = EffectiveFluidComponents(
        cartan_ghy_rho=_grid_function(a_grid, np.asarray(components_payload["cartan_ghy_rho"], dtype=float)),
        cartan_ghy_p=_grid_function(a_grid, np.asarray(components_payload["cartan_ghy_p"], dtype=float)),
        holst_nieh_yan_rho=_grid_function(a_grid, np.asarray(components_payload["holst_nieh_yan_rho"], dtype=float)),
        holst_nieh_yan_p=_grid_function(a_grid, np.asarray(components_payload["holst_nieh_yan_p"], dtype=float)),
        matter_flux_rho=_grid_function(a_grid, np.asarray(components_payload["matter_flux_rho"], dtype=float)),
        matter_flux_p=_grid_function(a_grid, np.asarray(components_payload["matter_flux_p"], dtype=float)),
        counterterm_rho=_grid_function(a_grid, np.asarray(components_payload["counterterm_rho"], dtype=float)),
        counterterm_p=_grid_function(a_grid, np.asarray(components_payload["counterterm_p"], dtype=float)),
    )
    rho_eff, _ = make_effective_fluid_functions(components)
    h_z2sigma = make_hubble_from_effective_density(
        float(payload["H0_Z2Sigma_km_s_Mpc"]),
        rho_eff,
        omega_k_z2sigma=float(payload.get("omega_k_Z2Sigma", 0.0)),
    )

    early = payload["early_plasma"]
    rho_baryon = _grid_function(z_grid, np.asarray(early["rho_baryon_Z2Sigma"], dtype=float))
    rho_photon = _grid_function(z_grid, np.asarray(early["rho_photon_Z2Sigma"], dtype=float))
    gamma_drag = _grid_function(z_grid, np.asarray(early["Gamma_drag_Z2Sigma"], dtype=float))
    cs_z2sigma = make_photon_baryon_sound_speed(rho_baryon, rho_photon)
    if payload.get("z_d_bracket") is None:
        positive_z_grid = z_grid[z_grid > 0.0]
        z_low, z_high = find_drag_epoch_bracket_z2sigma(h_z2sigma, gamma_drag, positive_z_grid)
    else:
        z_low, z_high = [float(value) for value in payload["z_d_bracket"]]
    z_d = solve_drag_epoch_z2sigma(h_z2sigma, gamma_drag, z_low=z_low, z_high=z_high)

    return write_active_z2sigma_bao_manifest(
        output_manifest_path,
        z_grid,
        h_z2sigma,
        cs_z2sigma,
        z_d,
        float(payload.get("z_max", z_grid[-1])),
        omega_k_z2sigma=float(payload.get("omega_k_Z2Sigma", 0.0)),
        input_provenance={
            "H_Z2Sigma": "active_effective_fluid_background_component_manifest",
            "c_s_Z2Sigma": "active_early_plasma_component_manifest",
            "z_d_Z2Sigma": "active_Gamma_drag_equals_H_solver",
            "r_d_Z2Sigma": "active_sound_ruler_integrator",
        },
        source_component_manifest_sha256=hashlib.sha256(
            Path(component_manifest_path).read_bytes()
        ).hexdigest(),
        source_component_manifest_path=str(component_manifest_path),
    )


def write_scale_free_bao_manifest_from_active_component_manifest(
    component_manifest_path: Path,
    output_manifest_path: Path,
) -> Path:
    """Create strict scale-free BAO inputs from active component arrays."""

    payload = _require_active_payload(component_manifest_path)
    a_grid = np.asarray(payload["a_grid"], dtype=float)
    z_grid = np.asarray(payload["z_grid"], dtype=float)
    if np.any(a_grid <= 0) or np.any(np.diff(a_grid) <= 0):
        raise ValueError("a_grid must be positive and strictly increasing")
    if np.any(z_grid < 0) or np.any(np.diff(z_grid) <= 0):
        raise ValueError("z_grid must be non-negative and strictly increasing")

    components_payload = payload["flrw_components_over_rho_crit0"]
    components = EffectiveFluidComponents(
        cartan_ghy_rho=_grid_function(a_grid, np.asarray(components_payload["cartan_ghy_rho"], dtype=float)),
        cartan_ghy_p=_grid_function(a_grid, np.asarray(components_payload["cartan_ghy_p"], dtype=float)),
        holst_nieh_yan_rho=_grid_function(a_grid, np.asarray(components_payload["holst_nieh_yan_rho"], dtype=float)),
        holst_nieh_yan_p=_grid_function(a_grid, np.asarray(components_payload["holst_nieh_yan_p"], dtype=float)),
        matter_flux_rho=_grid_function(a_grid, np.asarray(components_payload["matter_flux_rho"], dtype=float)),
        matter_flux_p=_grid_function(a_grid, np.asarray(components_payload["matter_flux_p"], dtype=float)),
        counterterm_rho=_grid_function(a_grid, np.asarray(components_payload["counterterm_rho"], dtype=float)),
        counterterm_p=_grid_function(a_grid, np.asarray(components_payload["counterterm_p"], dtype=float)),
    )
    rho_eff, _ = make_effective_fluid_functions(components)
    e_z2sigma = make_dimensionless_hubble_from_effective_density(
        rho_eff,
        omega_k_z2sigma=float(payload.get("omega_k_Z2Sigma", 0.0)),
    )

    early = payload["early_plasma"]
    rho_baryon = _grid_function(z_grid, np.asarray(early["rho_baryon_Z2Sigma"], dtype=float))
    rho_photon = _grid_function(z_grid, np.asarray(early["rho_photon_Z2Sigma"], dtype=float))
    gamma_drag = _grid_function(z_grid, np.asarray(early["Gamma_drag_Z2Sigma"], dtype=float))
    cs_over_c = make_photon_baryon_sound_speed_over_c(rho_baryon, rho_photon)
    gamma_over_h0 = make_drag_rate_over_h0_z2sigma(
        gamma_drag,
        float(payload["H0_Z2Sigma_km_s_Mpc"]),
    )
    if payload.get("z_d_bracket") is None:
        positive_z_grid = z_grid[z_grid > 0.0]
        z_low, z_high = find_drag_epoch_bracket_z2sigma(e_z2sigma, gamma_over_h0, positive_z_grid)
    else:
        z_low, z_high = [float(value) for value in payload["z_d_bracket"]]
    z_d = solve_drag_epoch_z2sigma(e_z2sigma, gamma_over_h0, z_low=z_low, z_high=z_high)

    return write_active_z2sigma_scale_free_bao_manifest(
        output_manifest_path,
        z_grid,
        e_z2sigma,
        cs_over_c,
        z_d,
        float(payload.get("z_max", z_grid[-1])),
        omega_k_z2sigma=float(payload.get("omega_k_Z2Sigma", 0.0)),
        gamma_drag_over_h0_z2sigma=gamma_over_h0,
        input_provenance={
            "E_Z2Sigma": "active_effective_fluid_dimensionless_background_component_manifest",
            "c_s_over_c_Z2Sigma": "active_early_plasma_component_manifest",
            "z_d_Z2Sigma": "active_scale_free_Gamma_drag_over_H0_equals_E_solver",
            "rhat_d_Z2Sigma": "active_dimensionless_sound_ruler_integrator",
        },
        source_component_manifest_sha256=hashlib.sha256(
            Path(component_manifest_path).read_bytes()
        ).hexdigest(),
        source_component_manifest_path=str(component_manifest_path),
    )


def write_scale_free_split_primitive_manifests_from_active_component_manifest(
    component_manifest_path: Path,
    background_primitive_path: Path,
    plasma_primitive_path: Path,
) -> tuple[Path, Path]:
    """Create split scale-free primitive manifests from active component arrays."""

    payload = _require_active_payload(component_manifest_path)
    a_grid = np.asarray(payload["a_grid"], dtype=float)
    z_grid = np.asarray(payload["z_grid"], dtype=float)
    if np.any(a_grid <= 0) or np.any(np.diff(a_grid) <= 0):
        raise ValueError("a_grid must be positive and strictly increasing")
    if np.any(z_grid < 0) or np.any(np.diff(z_grid) <= 0):
        raise ValueError("z_grid must be non-negative and strictly increasing")

    components_payload = payload["flrw_components_over_rho_crit0"]
    components = EffectiveFluidComponents(
        cartan_ghy_rho=_grid_function(a_grid, np.asarray(components_payload["cartan_ghy_rho"], dtype=float)),
        cartan_ghy_p=_grid_function(a_grid, np.asarray(components_payload["cartan_ghy_p"], dtype=float)),
        holst_nieh_yan_rho=_grid_function(a_grid, np.asarray(components_payload["holst_nieh_yan_rho"], dtype=float)),
        holst_nieh_yan_p=_grid_function(a_grid, np.asarray(components_payload["holst_nieh_yan_p"], dtype=float)),
        matter_flux_rho=_grid_function(a_grid, np.asarray(components_payload["matter_flux_rho"], dtype=float)),
        matter_flux_p=_grid_function(a_grid, np.asarray(components_payload["matter_flux_p"], dtype=float)),
        counterterm_rho=_grid_function(a_grid, np.asarray(components_payload["counterterm_rho"], dtype=float)),
        counterterm_p=_grid_function(a_grid, np.asarray(components_payload["counterterm_p"], dtype=float)),
    )
    rho_eff, _ = make_effective_fluid_functions(components)
    e_z2sigma = make_dimensionless_hubble_from_effective_density(
        rho_eff,
        omega_k_z2sigma=float(payload.get("omega_k_Z2Sigma", 0.0)),
    )

    early = payload["early_plasma"]
    rho_baryon = _grid_function(z_grid, np.asarray(early["rho_baryon_Z2Sigma"], dtype=float))
    rho_photon = _grid_function(z_grid, np.asarray(early["rho_photon_Z2Sigma"], dtype=float))
    gamma_drag = _grid_function(z_grid, np.asarray(early["Gamma_drag_Z2Sigma"], dtype=float))
    cs_over_c = make_photon_baryon_sound_speed_over_c(rho_baryon, rho_photon)
    gamma_over_h0 = make_drag_rate_over_h0_z2sigma(
        gamma_drag,
        float(payload["H0_Z2Sigma_km_s_Mpc"]),
    )
    z_d_bracket = payload.get("z_d_bracket")
    background = write_active_z2sigma_scale_free_background_primitive_manifest(
        background_primitive_path,
        z_grid,
        e_z2sigma,
        omega_k_z2sigma=float(payload.get("omega_k_Z2Sigma", 0.0)),
        z_max=float(payload.get("z_max", z_grid[-1])),
        primitive_provenance={
            "E_Z2Sigma": "active_effective_fluid_dimensionless_background_component_manifest",
            "omega_k_Z2Sigma": "active_projective_curvature_component_manifest",
        },
        z_d_bracket=z_d_bracket,
    )
    plasma = write_active_z2sigma_scale_free_plasma_primitive_manifest(
        plasma_primitive_path,
        z_grid,
        cs_over_c,
        gamma_over_h0,
        z_max=float(payload.get("z_max", z_grid[-1])),
        primitive_provenance={
            "c_s_over_c_Z2Sigma": "active_early_plasma_sound_speed_component_manifest",
            "Gamma_drag_over_H0_Z2Sigma": "active_thomson_drag_over_H0_component_manifest",
        },
        z_d_bracket=z_d_bracket,
    )
    return background, plasma


def _load_scale_free_omega_k_manifest(path: Path) -> tuple[float, str]:
    payload = json.loads(Path(path).read_text(encoding="utf-8"))
    if payload.get("active_core") != "Z2_tunnel_Sigma":
        raise ValueError("Scale-free omega_k manifest active_core must be Z2_tunnel_Sigma")
    if payload.get("source") != "active_derived":
        raise ValueError("Scale-free omega_k manifest source must be active_derived")
    for key in [
        "compressed_planck_lcdm_background_used",
        "archived_z4_background_reuse_used",
        "observational_H0_fit_used",
        "observational_curvature_fit_used",
    ]:
        if payload.get(key, False) is not False:
            raise ValueError(f"Forbidden omega_k provenance flag must be false: {key}")
    omega_k = float(payload["scalars"]["omega_k_Z2Sigma"])
    provenance = str(payload.get("scalar_provenance", {}).get("omega_k_Z2Sigma", "")).strip()
    if not provenance:
        raise ValueError("Missing omega_k_Z2Sigma provenance")
    lowered = provenance.lower()
    if any(token in lowered for token in FORBIDDEN_PROVENANCE_TOKENS):
        raise ValueError(f"Forbidden omega_k_Z2Sigma provenance: {provenance}")
    return omega_k, provenance


def write_scale_free_background_primitive_manifest_from_flrw_and_omega_k_manifests(
    flrw_component_manifest_path: Path,
    scale_free_omega_k_manifest_path: Path,
    background_primitive_path: Path,
    *,
    z_grid=None,
    z_max: float | None = None,
    z_d_bracket: list[float] | tuple[float, float] | None = None,
) -> Path:
    """Create scale-free background primitives without dimensional H0."""

    flrw = load_active_z2sigma_flrw_component_manifest(flrw_component_manifest_path)
    omega_k, omega_k_provenance = _load_scale_free_omega_k_manifest(
        scale_free_omega_k_manifest_path
    )
    a_grid = np.asarray(flrw["a_grid"], dtype=float)
    components_payload = flrw["flrw_components_over_rho_crit0"]
    components = EffectiveFluidComponents(
        cartan_ghy_rho=_grid_function(a_grid, np.asarray(components_payload["cartan_ghy_rho"], dtype=float)),
        cartan_ghy_p=_grid_function(a_grid, np.asarray(components_payload["cartan_ghy_p"], dtype=float)),
        holst_nieh_yan_rho=_grid_function(a_grid, np.asarray(components_payload["holst_nieh_yan_rho"], dtype=float)),
        holst_nieh_yan_p=_grid_function(a_grid, np.asarray(components_payload["holst_nieh_yan_p"], dtype=float)),
        matter_flux_rho=_grid_function(a_grid, np.asarray(components_payload["matter_flux_rho"], dtype=float)),
        matter_flux_p=_grid_function(a_grid, np.asarray(components_payload["matter_flux_p"], dtype=float)),
        counterterm_rho=_grid_function(a_grid, np.asarray(components_payload["counterterm_rho"], dtype=float)),
        counterterm_p=_grid_function(a_grid, np.asarray(components_payload["counterterm_p"], dtype=float)),
    )
    rho_eff, _ = make_effective_fluid_functions(components)
    e_z2sigma = make_dimensionless_hubble_from_effective_density(
        rho_eff,
        omega_k_z2sigma=omega_k,
    )
    if z_grid is None:
        a_min = float(a_grid[0])
        z_limit = (1.0 / a_min) - 1.0
        z_values = np.geomspace(1.0, 1.0 + z_limit, len(a_grid)) - 1.0
    else:
        z_values = np.asarray(z_grid, dtype=float)
    if z_max is None:
        z_max = float(z_values[-1])
    return write_active_z2sigma_scale_free_background_primitive_manifest(
        background_primitive_path,
        z_values,
        e_z2sigma,
        omega_k_z2sigma=omega_k,
        z_max=float(z_max),
        primitive_provenance={
            "E_Z2Sigma": "active_flrw_effective_density_dimensionless_builder",
            "omega_k_Z2Sigma": omega_k_provenance,
        },
        z_d_bracket=z_d_bracket,
    )


def write_scale_free_background_primitive_normalization_inputs_from_flrw_and_omega_k_manifests(
    flrw_component_manifest_path: Path,
    scale_free_omega_k_manifest_path: Path,
    output_path: Path,
    *,
    z_grid=None,
    z_max: float | None = None,
    z_d_bracket: list[float] | tuple[float, float] | None = None,
) -> Path:
    """Create direct background primitive normalization inputs from active manifests."""

    flrw = load_active_z2sigma_flrw_component_manifest(flrw_component_manifest_path)
    omega_k, omega_k_provenance = _load_scale_free_omega_k_manifest(
        scale_free_omega_k_manifest_path
    )
    a_grid = np.asarray(flrw["a_grid"], dtype=float)
    components_payload = flrw["flrw_components_over_rho_crit0"]
    components = EffectiveFluidComponents(
        cartan_ghy_rho=_grid_function(a_grid, np.asarray(components_payload["cartan_ghy_rho"], dtype=float)),
        cartan_ghy_p=_grid_function(a_grid, np.asarray(components_payload["cartan_ghy_p"], dtype=float)),
        holst_nieh_yan_rho=_grid_function(a_grid, np.asarray(components_payload["holst_nieh_yan_rho"], dtype=float)),
        holst_nieh_yan_p=_grid_function(a_grid, np.asarray(components_payload["holst_nieh_yan_p"], dtype=float)),
        matter_flux_rho=_grid_function(a_grid, np.asarray(components_payload["matter_flux_rho"], dtype=float)),
        matter_flux_p=_grid_function(a_grid, np.asarray(components_payload["matter_flux_p"], dtype=float)),
        counterterm_rho=_grid_function(a_grid, np.asarray(components_payload["counterterm_rho"], dtype=float)),
        counterterm_p=_grid_function(a_grid, np.asarray(components_payload["counterterm_p"], dtype=float)),
    )
    rho_eff, _ = make_effective_fluid_functions(components)
    e_z2sigma = make_dimensionless_hubble_from_effective_density(
        rho_eff,
        omega_k_z2sigma=omega_k,
    )
    if z_grid is None:
        a_min = float(a_grid[0])
        z_values = np.geomspace(1.0, 1.0 / a_min, len(a_grid)) - 1.0
    else:
        z_values = np.asarray(z_grid, dtype=float)
    if z_max is None:
        z_max = float(z_values[-1])
    payload = {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_rd_used": False,
        "archived_z4_reuse_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "observational_H0_fit_used": False,
        "z_grid": z_values.tolist(),
        "E_Z2Sigma": np.asarray(e_z2sigma(z_values), dtype=float).tolist(),
        "omega_k_Z2Sigma": float(omega_k),
        "z_max": float(z_max),
        "z_d_bracket": None if z_d_bracket is None else [float(v) for v in z_d_bracket],
        "primitive_provenance": {
            "E_Z2Sigma": "active_flrw_effective_density_dimensionless_builder",
            "omega_k_Z2Sigma": omega_k_provenance,
        },
    }
    destination = Path(output_path)
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    return destination


def _load_active_h0_scalar_manifest(path: Path) -> tuple[float, str]:
    payload = json.loads(Path(path).read_text(encoding="utf-8"))
    built = build_active_z2sigma_background_scalar_payload(
        payload,
        "H0_Z2Sigma_km_s_Mpc",
    )
    h0 = float(built["scalars"]["H0_Z2Sigma_km_s_Mpc"])
    provenance = str(built["scalar_provenance"]["H0_Z2Sigma"]).strip()
    return h0, provenance


def write_scale_free_plasma_primitive_manifest_from_early_plasma_and_h0_manifests(
    early_plasma_manifest_path: Path,
    h0_manifest_path: Path,
    plasma_primitive_path: Path,
) -> Path:
    """Create scale-free plasma primitives from active early plasma and H0."""

    early = load_active_z2sigma_early_plasma_manifest(early_plasma_manifest_path)
    h0, h0_provenance = _load_active_h0_scalar_manifest(h0_manifest_path)
    z_grid = np.asarray(early["z_grid"], dtype=float)
    early_payload = early["early_plasma"]
    rho_baryon = _grid_function(
        z_grid,
        np.asarray(early_payload["rho_baryon_Z2Sigma"], dtype=float),
    )
    rho_photon = _grid_function(
        z_grid,
        np.asarray(early_payload["rho_photon_Z2Sigma"], dtype=float),
    )
    gamma_drag = _grid_function(
        z_grid,
        np.asarray(early_payload["Gamma_drag_Z2Sigma"], dtype=float),
    )
    cs_over_c = make_photon_baryon_sound_speed_over_c(rho_baryon, rho_photon)
    gamma_over_h0 = make_drag_rate_over_h0_z2sigma(gamma_drag, h0)
    return write_active_z2sigma_scale_free_plasma_primitive_manifest(
        plasma_primitive_path,
        z_grid,
        cs_over_c,
        gamma_over_h0,
        z_max=float(early.get("z_max", z_grid[-1])),
        primitive_provenance={
            "c_s_over_c_Z2Sigma": "active_early_plasma_sound_speed_derivation",
            "Gamma_drag_over_H0_Z2Sigma": (
                "active_thomson_drag_rate_divided_by_active_H0:"
                f"{h0_provenance}"
            ),
        },
        z_d_bracket=early.get("z_d_bracket"),
    )


def write_scale_free_plasma_primitive_normalization_inputs_from_early_plasma_and_h0_manifests(
    early_plasma_manifest_path: Path,
    h0_manifest_path: Path,
    output_path: Path,
) -> Path:
    """Create direct plasma primitive normalization inputs from active manifests."""

    early = load_active_z2sigma_early_plasma_manifest(early_plasma_manifest_path)
    h0, h0_provenance = _load_active_h0_scalar_manifest(h0_manifest_path)
    z_grid = np.asarray(early["z_grid"], dtype=float)
    early_payload = early["early_plasma"]
    rho_baryon = _grid_function(
        z_grid,
        np.asarray(early_payload["rho_baryon_Z2Sigma"], dtype=float),
    )
    rho_photon = _grid_function(
        z_grid,
        np.asarray(early_payload["rho_photon_Z2Sigma"], dtype=float),
    )
    gamma_drag = _grid_function(
        z_grid,
        np.asarray(early_payload["Gamma_drag_Z2Sigma"], dtype=float),
    )
    cs_over_c = make_photon_baryon_sound_speed_over_c(rho_baryon, rho_photon)
    gamma_over_h0 = make_drag_rate_over_h0_z2sigma(gamma_drag, h0)
    payload = {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_rd_used": False,
        "archived_z4_reuse_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "observational_H0_fit_used": False,
        "z_grid": z_grid.tolist(),
        "c_s_over_c_Z2Sigma": np.asarray(cs_over_c(z_grid), dtype=float).tolist(),
        "Gamma_drag_over_H0_Z2Sigma": np.asarray(gamma_over_h0(z_grid), dtype=float).tolist(),
        "z_max": float(early.get("z_max", z_grid[-1])),
        "z_d_bracket": early.get("z_d_bracket"),
        "primitive_provenance": {
            "c_s_over_c_Z2Sigma": "active_early_plasma_sound_speed_derivation",
            "Gamma_drag_over_H0_Z2Sigma": (
                "active_thomson_drag_rate_divided_by_active_H0:"
                f"{h0_provenance}"
            ),
        },
    }
    destination = Path(output_path)
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    return destination


def write_scale_free_bao_manifest_from_primitive_manifest(
    primitive_manifest_path: Path,
    output_manifest_path: Path,
) -> Path:
    """Create strict scale-free BAO inputs from active dimensionless primitives."""

    primitive = load_active_z2sigma_scale_free_primitive_inputs(primitive_manifest_path)
    if primitive.z_d_bracket is None:
        positive_z_grid = primitive.z_grid[primitive.z_grid > 0.0]
        z_low, z_high = find_drag_epoch_bracket_z2sigma(
            primitive.e_z2sigma,
            primitive.gamma_drag_over_h0_z2sigma,
            positive_z_grid,
        )
    else:
        z_low, z_high = primitive.z_d_bracket
    z_d = solve_drag_epoch_z2sigma(
        primitive.e_z2sigma,
        primitive.gamma_drag_over_h0_z2sigma,
        z_low=z_low,
        z_high=z_high,
    )

    return write_active_z2sigma_scale_free_bao_manifest(
        output_manifest_path,
        primitive.z_grid,
        primitive.e_z2sigma,
        primitive.cs_over_c_z2sigma,
        z_d,
        primitive.z_max,
        omega_k_z2sigma=primitive.omega_k_z2sigma,
        gamma_drag_over_h0_z2sigma=primitive.gamma_drag_over_h0_z2sigma,
        input_provenance={
            "E_Z2Sigma": "active_scale_free_primitive_manifest",
            "c_s_over_c_Z2Sigma": "active_scale_free_primitive_manifest",
            "z_d_Z2Sigma": "active_scale_free_Gamma_drag_over_H0_equals_E_solver",
            "rhat_d_Z2Sigma": "active_dimensionless_sound_ruler_integrator",
        },
        source_component_manifest_sha256=hashlib.sha256(
            Path(primitive_manifest_path).read_bytes()
        ).hexdigest(),
        source_component_manifest_path=str(primitive_manifest_path),
    )


def write_scale_free_primitive_manifest_from_split_manifests(
    background_primitive_path: Path,
    plasma_primitive_path: Path,
    output_manifest_path: Path,
) -> Path:
    """Merge active dimensionless background and plasma primitives into BAO primitives."""

    background = load_active_z2sigma_scale_free_background_primitive_inputs(
        background_primitive_path
    )
    plasma = load_active_z2sigma_scale_free_plasma_primitive_inputs(plasma_primitive_path)
    z_grid = background.z_grid
    plasma_z_grid = plasma.z_grid
    if z_grid.shape != plasma_z_grid.shape or np.max(np.abs(z_grid - plasma_z_grid)) > 1.0e-12:
        raise ValueError("Scale-free split primitive z_grid values must be aligned")
    z_max = background.z_max
    if not np.isclose(z_max, plasma.z_max, rtol=0.0, atol=1.0e-12):
        raise ValueError("Scale-free split primitive z_max values must match")
    background_payload = json.loads(Path(background_primitive_path).read_text(encoding="utf-8"))
    plasma_payload = json.loads(Path(plasma_primitive_path).read_text(encoding="utf-8"))
    return write_active_z2sigma_scale_free_primitive_manifest(
        output_manifest_path,
        z_grid,
        background.e_z2sigma,
        plasma.cs_over_c_z2sigma,
        plasma.gamma_drag_over_h0_z2sigma,
        background.omega_k_z2sigma,
        z_max,
        primitive_provenance={
            "E_Z2Sigma": background_payload["primitive_provenance"]["E_Z2Sigma"],
            "c_s_over_c_Z2Sigma": plasma_payload["primitive_provenance"]["c_s_over_c_Z2Sigma"],
            "Gamma_drag_over_H0_Z2Sigma": plasma_payload["primitive_provenance"][
                "Gamma_drag_over_H0_Z2Sigma"
            ],
            "omega_k_Z2Sigma": background_payload["primitive_provenance"]["omega_k_Z2Sigma"],
        },
        z_d_bracket=background.z_d_bracket or plasma.z_d_bracket,
    )
