from __future__ import annotations

import json
import sys
from pathlib import Path
from typing import Callable

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from janus_lab.z2_sigma_background_inputs import (
    load_active_z2sigma_background_scalar_input_manifest,
)
from janus_lab.z2_sigma_early_plasma_inputs import (
    load_active_z2sigma_early_plasma_input_manifest,
)
from janus_lab.z2_sigma_flrw_component_inputs import (
    load_active_z2sigma_flrw_component_input_manifest,
)
from janus_lab.z2_sigma_active_pipeline import _load_scale_free_omega_k_manifest


BACKGROUND_INPUT_PATH = Path("outputs/active_z2_sigma/background_scalar_inputs.json")
OMEGA_K_INPUT_PATH = Path("outputs/active_z2_sigma/background_scale_free_omega_k_inputs.json")
FLRW_INPUT_PATH = Path("outputs/active_z2_sigma/flrw_component_inputs.json")
EARLY_INPUT_PATH = Path("outputs/active_z2_sigma/early_plasma_inputs.json")
REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_bao_active_primitive_physical_input_obligation_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_bao_active_primitive_physical_input_obligation_gate.json"
)


def _status(path: Path, loader: Callable[[Path], dict]) -> dict:
    exists = path.exists()
    valid = False
    error = None
    if exists:
        try:
            loader(path)
            valid = True
        except Exception as exc:
            error = str(exc)
    return {"path": str(path), "exists": exists, "valid": valid, "validation_error": error}


def build_payload(
    *,
    background_input_path: Path = BACKGROUND_INPUT_PATH,
    omega_k_input_path: Path = OMEGA_K_INPUT_PATH,
    flrw_input_path: Path = FLRW_INPUT_PATH,
    early_input_path: Path = EARLY_INPUT_PATH,
) -> dict:
    background = _status(background_input_path, load_active_z2sigma_background_scalar_input_manifest)
    omega_k = _status(omega_k_input_path, lambda path: {"omega_k": _load_scale_free_omega_k_manifest(path)})
    flrw = _status(flrw_input_path, load_active_z2sigma_flrw_component_input_manifest)
    early = _status(early_input_path, load_active_z2sigma_early_plasma_input_manifest)
    ready = {
        "scale_free_omega_k_inputs": omega_k["valid"],
        "flrw_component_inputs": flrw["valid"],
        "early_plasma_inputs": early["valid"],
    }
    missing = [name for name, ok in ready.items() if not ok]
    next_by_group = {
        "scale_free_omega_k_inputs": "derive_or_supply_scale_free_omega_k_inputs_from_active_Z2Sigma_only",
        "flrw_component_inputs": "derive_or_supply_flrw_component_inputs_from_active_Z2Sigma_only",
        "early_plasma_inputs": "derive_or_supply_early_plasma_inputs_from_active_Z2Sigma_only",
    }
    return {
        "status": "janus-z2-sigma-bao-active-primitive-physical-input-obligation-gate",
        "active_core": "Z2_tunnel_Sigma",
        "bibliography_checked": True,
        "policy": {
            "compressed_planck_lcdm_forbidden": True,
            "archived_z4_forbidden": True,
            "observational_H0_fit_forbidden": True,
            "phenomenological_holst_bao_scan_forbidden": True,
            "mock_active_inputs_forbidden": True,
        },
        "required_active_input_manifests": {
            "background_scalar_inputs_legacy_dimensional_path": background,
            "scale_free_omega_k_inputs": omega_k,
            "flrw_component_inputs": flrw,
            "early_plasma_inputs": early,
        },
        "physical_input_groups_ready": ready,
        "missing_physical_input_groups": missing,
        "primitive_obligations": {
            "E_Z2Sigma": [
                "scale_free_omega_k_inputs",
                "flrw_component_inputs",
                "effective_fluid_numeric_closure",
            ],
            "omega_k_Z2Sigma": [
                "scale_free_omega_k_inputs",
                "active_projective_curvature_scale_free_branch",
            ],
            "c_s_over_c_Z2Sigma": [
                "early_plasma_inputs",
                "active_baryon_photon_density_history",
            ],
            "Gamma_drag_over_H0_Z2Sigma": [
                "early_plasma_inputs",
                "scale_free_omega_k_inputs",
                "active_free_electron_history",
            ],
        },
        "scale_free_primitive_physics_ready": all(ready.values()),
        "desi_dr2_bao_chi2_allowed": all(ready.values()),
        "gate_passed": all(ready.values()),
        "blocker": (
            "missing active physical input manifests"
            if missing
            else "active physical inputs available"
        ),
        "next_required": [next_by_group[item] for item in missing]
        + ["then_run_active_inputs_to_scale_free_primitive_chi2_gate"],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma BAO Active Primitive Physical Input Obligation Gate",
        "",
        f"Scale-free omega_k inputs valid: `{payload['physical_input_groups_ready']['scale_free_omega_k_inputs']}`",
        f"FLRW inputs valid: `{payload['physical_input_groups_ready']['flrw_component_inputs']}`",
        f"Early-plasma inputs valid: `{payload['physical_input_groups_ready']['early_plasma_inputs']}`",
        f"Scale-free primitive physics ready: `{payload['scale_free_primitive_physics_ready']}`",
        f"DESI DR2 BAO chi2 allowed: `{payload['desi_dr2_bao_chi2_allowed']}`",
        f"Gate passed: `{payload['gate_passed']}`",
        "",
        "## Missing Physical Input Groups",
    ]
    lines.extend(f"- `{item}`" for item in payload["missing_physical_input_groups"])
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
