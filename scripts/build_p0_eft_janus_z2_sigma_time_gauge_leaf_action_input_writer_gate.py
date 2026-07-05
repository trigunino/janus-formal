from __future__ import annotations

import json
from pathlib import Path


INPUT_PATH = Path("outputs/active_z2_sigma/active_time_coordinate_parity_inputs.json")
OUTPUT_PATH = Path("outputs/active_z2_sigma/time_gauge_leaf_action_inputs.json")
REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_time_gauge_leaf_action_input_writer_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_time_gauge_leaf_action_input_writer_gate.json"
)


def _load(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def _build_output(payload: dict) -> dict:
    if payload.get("active_core") != "Z2_tunnel_Sigma":
        raise ValueError("Input active_core must be Z2_tunnel_Sigma")
    if payload.get("source") != "active_derived":
        raise ValueError("Input source must be active_derived")
    for key in [
        "compressed_planck_lcdm_background_used",
        "archived_z4_background_reuse_used",
        "observational_curvature_fit_used",
        "observational_time_gauge_fit_used",
    ]:
        if payload.get(key) is not False:
            raise ValueError(f"Forbidden provenance flag must be false: {key}")
    parity = payload.get("time_coordinate_parity", {})
    if parity.get("z2_equivariant_time_coordinate_derived") is not True:
        raise ValueError("z2_equivariant_time_coordinate_derived must be true")
    parity_type = parity.get("antipodal_time_parity")
    if parity_type == "even":
        leaf_action = "antipodal_invariant_leaf"
    elif parity_type == "odd":
        leaf_action = "antipodal_paired_leaves"
    else:
        raise ValueError("antipodal_time_parity must be even or odd")
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_background_reuse_used": False,
        "observational_curvature_fit_used": False,
        "time_gauge_leaf_action": {
            "z2_equivariant_time_gauge_derived": True,
            "flrw_slices_from_active_time_gauge": True,
            "leaf_action_type": leaf_action,
            "source_time_parity": parity_type,
        },
        "leaf_action_policy": {
            "even_time_parity_gives": "antipodal_invariant_leaf",
            "odd_time_parity_gives": "antipodal_paired_leaves",
            "branch_not_fit": True,
        },
    }


def build_payload(*, input_path: Path = INPUT_PATH, output_path: Path = OUTPUT_PATH) -> dict:
    input_exists = input_path.exists()
    output_written = False
    validation_error = None
    leaf_action = None
    if input_exists:
        try:
            output = _build_output(_load(input_path))
            output_path.parent.mkdir(parents=True, exist_ok=True)
            output_path.write_text(json.dumps(output, indent=2), encoding="utf-8")
            leaf_action = output["time_gauge_leaf_action"]["leaf_action_type"]
            output_written = True
        except Exception as exc:
            validation_error = str(exc)
    return {
        "status": "janus-z2-sigma-time-gauge-leaf-action-input-writer-gate",
        "active_core": "Z2_tunnel_Sigma",
        "input_manifest": str(input_path),
        "output_manifest": str(output_path),
        "input_exists": input_exists,
        "time_parity_to_leaf_action_rule_ready": True,
        "time_gauge_leaf_action_input_written": output_written,
        "leaf_action_type": leaf_action,
        "uses_compressed_planck_lcdm_background": False,
        "uses_archived_z4_background": False,
        "uses_observational_curvature_fit": False,
        "uses_observational_time_gauge_fit": False,
        "gate_passed": output_written,
        "validation_error": validation_error,
        "next_required": [
            "derive_active_Z2_equivariant_time_coordinate_parity",
            "write_outputs_active_z2_sigma_active_time_coordinate_parity_inputs_json",
            "run_projective_spatial_slice_topology_branch_gate",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Time-Gauge Leaf-Action Input Writer Gate",
        "",
        f"Input exists: `{payload['input_exists']}`",
        f"Rule ready: `{payload['time_parity_to_leaf_action_rule_ready']}`",
        f"Input written: `{payload['time_gauge_leaf_action_input_written']}`",
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
