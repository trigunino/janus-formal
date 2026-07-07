from __future__ import annotations

import json
import sys
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from janus_lab.z2_sigma_active_inputs import (
    load_active_z2sigma_scale_free_background_primitive_inputs,
)
from janus_lab.z2_sigma_active_pipeline import (
    write_scale_free_background_primitive_manifest_from_flrw_and_omega_k_manifests,
)


FLRW_COMPONENT_PATH = Path("outputs/active_z2_sigma/flrw_components.json")
OMEGA_K_PATH = Path("outputs/active_z2_sigma/background_scale_free_omega_k_inputs.json")
BACKGROUND_PRIMITIVE_PATH = Path(
    "outputs/active_z2_sigma/bao_scale_free_background_primitive_inputs.json"
)
REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_flrw_to_scale_free_background_primitive_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_flrw_to_scale_free_background_primitive_gate.json"
)


def _diagnose_e2(flrw_component_path: Path, omega_k_path: Path, z_grid=None) -> dict | None:
    if not (flrw_component_path.exists() and omega_k_path.exists()):
        return None
    flrw = json.loads(flrw_component_path.read_text(encoding="utf-8"))
    omega = json.loads(omega_k_path.read_text(encoding="utf-8"))
    a_grid = np.asarray(flrw["a_grid"], dtype=float)
    components = flrw["flrw_components_over_rho_crit0"]
    rho_grid = np.zeros_like(a_grid, dtype=float)
    for key in [
        "cartan_ghy_rho",
        "holst_nieh_yan_rho",
        "matter_flux_rho",
        "counterterm_rho",
    ]:
        rho_grid = rho_grid + np.asarray(components[key], dtype=float)
    if z_grid is None:
        z_values = np.geomspace(1.0, 1.0 / float(a_grid[0]), len(a_grid)) - 1.0
    else:
        z_values = np.asarray(z_grid, dtype=float)
    a_values = 1.0 / (1.0 + z_values)
    rho_values = np.interp(a_values, a_grid, rho_grid)
    omega_k = float(omega["scalars"]["omega_k_Z2Sigma"])
    curvature_values = omega_k / (a_values * a_values)
    e2_values = rho_values + curvature_values
    min_index = int(np.argmin(e2_values))
    return {
        "rho_eff_min": float(np.min(rho_values)),
        "rho_eff_max": float(np.max(rho_values)),
        "omega_k": omega_k,
        "curvature_term_min": float(np.min(curvature_values)),
        "curvature_term_max": float(np.max(curvature_values)),
        "E2_min": float(e2_values[min_index]),
        "E2_min_at_z": float(z_values[min_index]),
        "E2_min_at_a": float(a_values[min_index]),
        "E2_positive_on_grid": bool(np.all(e2_values > 0.0)),
    }


def build_payload(
    *,
    flrw_component_path: Path = FLRW_COMPONENT_PATH,
    omega_k_path: Path = OMEGA_K_PATH,
    background_primitive_path: Path = BACKGROUND_PRIMITIVE_PATH,
    z_grid=None,
    z_max: float | None = None,
    z_d_bracket: list[float] | tuple[float, float] | None = None,
) -> dict:
    input_exists = {
        "flrw_components": flrw_component_path.exists(),
        "scale_free_omega_k": omega_k_path.exists(),
    }
    written = False
    valid = False
    validation_error = None
    omega_k_value = None
    z_grid_length = None
    e2_diagnostic = _diagnose_e2(flrw_component_path, omega_k_path, z_grid=z_grid)
    if all(input_exists.values()):
        try:
            path = write_scale_free_background_primitive_manifest_from_flrw_and_omega_k_manifests(
                flrw_component_path,
                omega_k_path,
                background_primitive_path,
                z_grid=z_grid,
                z_max=z_max,
                z_d_bracket=z_d_bracket,
            )
            written = True
            primitive = load_active_z2sigma_scale_free_background_primitive_inputs(path)
            valid = True
            omega_k_value = primitive.omega_k_z2sigma
            z_grid_length = int(len(primitive.z_grid))
        except Exception as exc:
            validation_error = str(exc)
    return {
        "status": "janus-z2-sigma-flrw-to-scale-free-background-primitive-gate",
        "active_core": "Z2_tunnel_Sigma",
        "input_manifests": {
            "flrw_components": str(flrw_component_path),
            "scale_free_omega_k": str(omega_k_path),
        },
        "input_exists": input_exists,
        "background_primitive_manifest": str(background_primitive_path),
        "background_primitive_written": written,
        "background_primitive_valid": valid,
        "omega_k_value": omega_k_value,
        "z_grid_length": z_grid_length,
        "E2_diagnostic": e2_diagnostic,
        "uses_compressed_planck_lcdm": False,
        "uses_archived_z4": False,
        "uses_observational_H0_fit": False,
        "gate_passed": valid,
        "validation_error": validation_error,
        "next_required": (
            [
                "derive_positive_active_Friedmann_source_or_valid_flat_limit",
                "do_not_add_fitted_density_to_fix_E2",
            ]
            if e2_diagnostic is not None
            and e2_diagnostic["E2_positive_on_grid"] is False
            else [
                "supply_outputs_active_z2_sigma_flrw_components_json",
                "pass_scale_free_omega_k_from_curvature_scale_gate",
                "merge_background_and_plasma_primitives",
            ]
        ),
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma FLRW To Scale-Free Background Primitive Gate",
        "",
        f"Input exists: `{payload['input_exists']}`",
        f"Background primitive written: `{payload['background_primitive_written']}`",
        f"Background primitive valid: `{payload['background_primitive_valid']}`",
        f"Gate passed: `{payload['gate_passed']}`",
    ]
    if payload["validation_error"]:
        lines.extend(["", "## Validation Error", payload["validation_error"]])
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
