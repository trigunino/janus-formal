from __future__ import annotations

import json
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from scripts.build_p0_eft_janus_z2_sigma_projective_foliation_compatibility_gate import (
    build_payload as build_projective_foliation_compatibility_payload,
)


INPUT_PATH = Path("outputs/active_z2_sigma/projective_foliation_inputs.json")
OUTPUT_PATH = Path("outputs/active_z2_sigma/rp3_spatial_slice_inputs.json")
REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_rp3_spatial_slice_input_writer_from_projective_foliation_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_rp3_spatial_slice_input_writer_from_projective_foliation_gate.json"
)


def _load(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def _reject_forbidden(payload: dict) -> None:
    for key in [
        "compressed_planck_lcdm_background_used",
        "archived_z4_background_reuse_used",
        "observational_curvature_fit_used",
    ]:
        if payload.get(key) is not False:
            raise ValueError(f"Forbidden provenance flag must be false: {key}")


def _build_output(payload: dict) -> dict:
    if payload.get("active_core") != "Z2_tunnel_Sigma":
        raise ValueError("Input active_core must be Z2_tunnel_Sigma")
    if payload.get("source") != "active_derived":
        raise ValueError("Input source must be active_derived")
    _reject_forbidden(payload)

    foliation = payload.get("projective_foliation", {})
    required = {
        "ambient_cover": "S4",
        "ambient_quotient": "RP4",
        "spatial_cover_leaf": "S3",
        "spatial_quotient_leaf": "RP3",
    }
    for key, value in required.items():
        if foliation.get(key) != value:
            raise ValueError(f"{key} must be {value}")
    if foliation.get("antipodal_action_preserves_spatial_leaf") is not True:
        raise ValueError("antipodal_action_preserves_spatial_leaf must be true")
    if foliation.get("spatial_leaf_action_free") is not True:
        raise ValueError("spatial_leaf_action_free must be true")
    if foliation.get("flrw_slices_identified_with_spatial_leaves") is not True:
        raise ValueError("flrw_slices_identified_with_spatial_leaves must be true")

    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_background_reuse_used": False,
        "observational_curvature_fit_used": False,
        "spatial_topology": {
            "cover_spatial_slice": "S3",
            "quotient_spatial_slice": "RP3",
            "antipodal_Z2_quotient": True,
        },
        "topology_provenance": {
            "quotient_spatial_slice": "active_projective_foliation:S3_to_RP3",
        },
        "open_quantities": {
            "R_curv_Z2Sigma_still_required": True,
            "omega_k_Z2Sigma_not_computed_here": True,
        },
    }


def build_payload(*, input_path: Path = INPUT_PATH, output_path: Path = OUTPUT_PATH) -> dict:
    compatibility = build_projective_foliation_compatibility_payload()
    input_exists = input_path.exists()
    output_written = False
    validation_error = None
    if input_exists:
        try:
            output = _build_output(_load(input_path))
            output_path.parent.mkdir(parents=True, exist_ok=True)
            output_path.write_text(json.dumps(output, indent=2), encoding="utf-8")
            output_written = True
        except Exception as exc:
            validation_error = str(exc)

    return {
        "status": "janus-z2-sigma-rp3-spatial-slice-input-writer-from-projective-foliation-gate",
        "active_core": "Z2_tunnel_Sigma",
        "input_manifest": str(input_path),
        "output_manifest": str(output_path),
        "input_exists": input_exists,
        "projective_foliation_compatibility_gate_passed": compatibility["gate_passed"],
        "single_leaf_RP3_inference_allowed": compatibility[
            "single_leaf_RP3_inference_allowed"
        ],
        "projective_foliation_to_rp3_slice_rule_ready": True,
        "requires_active_foliation_not_topology_alone": True,
        "rp3_spatial_slice_input_written": output_written,
        "curvature_radius_still_required": True,
        "omega_k_not_computed_here": True,
        "uses_compressed_planck_lcdm_background": False,
        "uses_archived_z4_background": False,
        "uses_observational_curvature_fit": False,
        "gate_passed": output_written,
        "validation_error": validation_error,
        "next_required": list(dict.fromkeys([
            *compatibility["next_required"],
            "derive_active_projective_foliation_by_antipodal_S3_leaves",
            "write_outputs_active_z2_sigma_projective_foliation_inputs_json",
            "run_rp3_spatial_slice_curvature_sign_gate",
        ])),
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma RP3 Spatial Slice Input Writer From Projective Foliation Gate",
        "",
        f"Input exists: `{payload['input_exists']}`",
        f"Rule ready: `{payload['projective_foliation_to_rp3_slice_rule_ready']}`",
        f"Output written: `{payload['rp3_spatial_slice_input_written']}`",
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
