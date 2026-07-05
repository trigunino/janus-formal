from __future__ import annotations

import json
import sys
from pathlib import Path
from typing import Callable

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from janus_lab.z2_sigma_background_inputs import (
    build_active_z2sigma_background_scalar_payload,
    build_active_z2sigma_curvature_payload_from_flrw_branch,
)


H0_INPUT_PATH = Path("outputs/active_z2_sigma/background_H0_normalization_inputs.json")
CURVATURE_BRANCH_INPUT_PATH = Path(
    "outputs/active_z2_sigma/background_curvature_branch_inputs.json"
)
GRAVITY_INPUT_PATH = Path("outputs/active_z2_sigma/background_gravity_normalization_inputs.json")
REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_background_physical_input_obligation_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_background_physical_input_obligation_gate.json"
)


def _status(path: Path, builder: Callable[[dict], dict]) -> dict:
    exists = path.exists()
    valid = False
    error = None
    if exists:
        try:
            builder(json.loads(path.read_text(encoding="utf-8")))
            valid = True
        except Exception as exc:
            error = str(exc)
    return {"path": str(path), "exists": exists, "valid": valid, "validation_error": error}


def _h0_payload(payload: dict) -> dict:
    return build_active_z2sigma_background_scalar_payload(payload, "H0_Z2Sigma_km_s_Mpc")


def _gravity_payload(payload: dict) -> dict:
    return build_active_z2sigma_background_scalar_payload(
        payload,
        "gravitational_constant_si_Z2Sigma",
    )


def build_payload(
    *,
    h0_input_path: Path = H0_INPUT_PATH,
    curvature_branch_input_path: Path = CURVATURE_BRANCH_INPUT_PATH,
    gravity_input_path: Path = GRAVITY_INPUT_PATH,
) -> dict:
    h0 = _status(h0_input_path, _h0_payload)
    curvature = _status(
        curvature_branch_input_path,
        build_active_z2sigma_curvature_payload_from_flrw_branch,
    )
    gravity = _status(gravity_input_path, _gravity_payload)
    ready = {
        "H0_Z2Sigma": h0["valid"],
        "omega_k_Z2Sigma_from_FLRW_branch": curvature["valid"],
        "G_Z2Sigma": gravity["valid"],
    }
    missing = [name for name, ok in ready.items() if not ok]
    next_required = []
    if not h0["valid"]:
        next_required.append("derive_active_H0_Z2Sigma_scale_normalization")
    if not curvature["valid"]:
        next_required.append("derive_active_FLRW_spatial_metric_branch_k_and_Rcurv")
    if not gravity["valid"]:
        next_required.append("derive_or_declare_active_low_energy_G_Z2Sigma_convention")
    next_required.append("run_background_atomic_input_writers_and_assembler")
    return {
        "status": "janus-z2-sigma-background-physical-input-obligation-gate",
        "active_core": "Z2_tunnel_Sigma",
        "bibliography_checked": True,
        "primary_sources_checked": [
            "standard FLRW curvature convention Omega_k=-k c^2/(H0^2 R_curv^2)",
            "Friedmann normalization rho_crit0=3 H0^2/(8 pi G)",
            "projective/tunnel topology does not by itself fix numeric H0, G, k, or R_curv",
        ],
        "required_inputs": {
            "H0_normalization": h0,
            "curvature_branch": curvature,
            "gravity_normalization": gravity,
        },
        "background_physical_inputs_ready": all(ready.values()),
        "physical_input_groups_ready": ready,
        "missing_physical_inputs": missing,
        "omega_k_formula_ready": True,
        "omega_k_formula": "omega_k_Z2Sigma = -k_Z2Sigma*c^2/(H0_Z2Sigma^2*R_curv_Z2Sigma^2)",
        "requires_active_H0_for_E_Z2Sigma": True,
        "requires_active_flrw_components_for_E_Z2Sigma": True,
        "requires_active_curvature_branch_for_omega_k": True,
        "uses_compressed_planck_lcdm_background": False,
        "uses_archived_z4_background": False,
        "uses_observational_H0_fit": False,
        "uses_observational_curvature_fit": False,
        "mock_inputs_forbidden": True,
        "gate_passed": all(ready.values()),
        "next_required": next_required,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Background Physical Input Obligation Gate",
        "",
        f"H0 input valid: `{payload['required_inputs']['H0_normalization']['valid']}`",
        f"Curvature branch valid: `{payload['required_inputs']['curvature_branch']['valid']}`",
        f"G input valid: `{payload['required_inputs']['gravity_normalization']['valid']}`",
        f"Background physical inputs ready: `{payload['background_physical_inputs_ready']}`",
        f"Gate passed: `{payload['gate_passed']}`",
        "",
        "## Missing Physical Inputs",
    ]
    lines.extend(f"- `{item}`" for item in payload["missing_physical_inputs"])
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
