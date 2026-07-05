from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z2_sigma_background_h0_input_writer_gate import (
    build_payload as build_h0_writer_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_background_curvature_radius_input_writer_gate import (
    build_payload as build_radius_writer_payload,
)


H0_INPUT_PATH = Path("outputs/active_z2_sigma/background_H0_inputs.json")
SIGN_INPUT_PATH = Path("outputs/active_z2_sigma/background_curvature_sign_inputs.json")
RADIUS_INPUT_PATH = Path("outputs/active_z2_sigma/background_curvature_radius_inputs.json")
OUTPUT_PATH = Path("outputs/active_z2_sigma/background_curvature_branch_inputs.json")
REPORT_PATH = Path(
    "outputs/reports/"
    "p0_eft_janus_z2_sigma_background_curvature_branch_inputs_assembler_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/"
    "p0_eft_janus_z2_sigma_background_curvature_branch_inputs_assembler_gate.json"
)


def _load(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def _validate_base(payload: dict, *, forbid_h0_fit: bool = True) -> None:
    if payload.get("active_core") != "Z2_tunnel_Sigma":
        raise ValueError("Input active_core must be Z2_tunnel_Sigma")
    if payload.get("source") != "active_derived":
        raise ValueError("Input source must be active_derived")
    for key in ["compressed_planck_lcdm_background_used", "archived_z4_background_reuse_used"]:
        if payload.get(key) is not False:
            raise ValueError(f"Forbidden provenance flag must be false: {key}")
    if forbid_h0_fit and payload.get("observational_H0_fit_used") is not False:
        raise ValueError("observational_H0_fit_used must be false")
    if payload.get("observational_curvature_fit_used", False) is not False:
        raise ValueError("observational_curvature_fit_used must be false")


def _build_output(h0: dict, sign: dict, radius: dict) -> dict:
    _validate_base(h0)
    _validate_base(sign, forbid_h0_fit=False)
    _validate_base(radius, forbid_h0_fit=False)

    h0_value = float(h0["scalars"]["H0_Z2Sigma_km_s_Mpc"])
    k_value = int(sign["scalars"]["k_Z2Sigma"])
    radius_value = float(radius["scalars"]["R_curv_Z2Sigma_Mpc"])
    if h0_value <= 0.0:
        raise ValueError("H0_Z2Sigma_km_s_Mpc must be positive")
    if k_value not in [-1, 0, 1]:
        raise ValueError("k_Z2Sigma must be -1, 0, or 1")
    if radius_value <= 0.0:
        raise ValueError("R_curv_Z2Sigma_Mpc must be positive")

    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_background_reuse_used": False,
        "observational_H0_fit_used": False,
        "observational_curvature_fit_used": False,
        "scalars": {
            "H0_Z2Sigma_km_s_Mpc": h0_value,
            "R_curv_Z2Sigma_Mpc": radius_value,
            "k_Z2Sigma": k_value,
        },
        "scalar_provenance": {
            "H0_Z2Sigma": h0["scalar_provenance"]["H0_Z2Sigma"],
            "R_curv_Z2Sigma": radius["scalar_provenance"]["R_curv_Z2Sigma"],
            "k_Z2Sigma": sign["scalar_provenance"]["k_Z2Sigma"],
        },
        "spatial_topology": sign.get("spatial_topology", {}),
    }


def build_payload(
    *,
    h0_input_path: Path = H0_INPUT_PATH,
    sign_input_path: Path = SIGN_INPUT_PATH,
    radius_input_path: Path = RADIUS_INPUT_PATH,
    output_path: Path = OUTPUT_PATH,
) -> dict:
    h0_writer = build_h0_writer_payload(output_path=h0_input_path)
    radius_writer = build_radius_writer_payload(output_path=radius_input_path)
    input_exists = {
        "h0": h0_input_path.exists(),
        "curvature_sign": sign_input_path.exists(),
        "curvature_radius": radius_input_path.exists(),
    }
    output_written = False
    validation_error = None
    if all(input_exists.values()):
        try:
            output = _build_output(
                _load(h0_input_path),
                _load(sign_input_path),
                _load(radius_input_path),
            )
            output_path.parent.mkdir(parents=True, exist_ok=True)
            output_path.write_text(json.dumps(output, indent=2), encoding="utf-8")
            output_written = True
        except Exception as exc:
            validation_error = str(exc)

    return {
        "status": "janus-z2-sigma-background-curvature-branch-inputs-assembler-gate",
        "active_core": "Z2_tunnel_Sigma",
        "input_manifests": {
            "h0": str(h0_input_path),
            "curvature_sign": str(sign_input_path),
            "curvature_radius": str(radius_input_path),
        },
        "upstream_writer_gates": {
            "h0": {
                "gate": h0_writer["status"],
                "passed": h0_writer["gate_passed"],
                "missing_active_artifact": h0_writer["missing_active_artifact"],
            },
            "curvature_radius": {
                "gate": radius_writer["status"],
                "passed": radius_writer["gate_passed"],
                "missing_active_artifact": radius_writer["missing_active_artifact"],
            },
        },
        "nearest_background_curvature_branch_frontier": {
            "blocks": [
                "active_H0_Z2Sigma_scale_normalization",
                "active_R_curv_Z2Sigma_Mpc_from_embedding_or_throat_scale",
            ],
            "gates": [
                "P0EFTJanusZ2SigmaBackgroundH0InputWriterGate",
                "P0EFTJanusZ2SigmaBackgroundCurvatureRadiusInputWriterGate",
            ],
            "diagnostic_only": True,
        },
        "output_manifest": str(output_path),
        "input_exists": input_exists,
        "curvature_branch_inputs_written": output_written,
        "uses_compressed_planck_lcdm_background": False,
        "uses_archived_z4_background": False,
        "uses_observational_H0_fit": False,
        "uses_observational_curvature_fit": False,
        "gate_passed": output_written,
        "primary_blocker": "none" if output_written else "active_H0_and_R_curv_inputs",
        "validation_error": validation_error,
        "next_required": [
            "supply_outputs_active_z2_sigma_background_H0_inputs_json",
            "supply_outputs_active_z2_sigma_background_curvature_sign_inputs_json",
            "derive_active_R_curv_Z2Sigma_Mpc",
            "supply_outputs_active_z2_sigma_background_curvature_radius_inputs_json",
            "run_background_curvature_normalization_from_branch_gate",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Background Curvature Branch Inputs Assembler Gate",
        "",
        f"Input exists: `{payload['input_exists']}`",
        f"Output written: `{payload['curvature_branch_inputs_written']}`",
        f"Gate passed: `{payload['gate_passed']}`",
        "",
        "## Next Required",
    ]
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    if payload["validation_error"]:
        lines.extend(["", "## Validation Error", payload["validation_error"]])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
