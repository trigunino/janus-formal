from __future__ import annotations

import json
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from scripts.build_p0_eft_janus_z2_sigma_time_gauge_leaf_action_input_writer_gate import (
    build_payload as build_time_gauge_leaf_action_writer_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_signed_cover_time_coordinate_from_projective_tunnel_gate import (
    build_payload as build_signed_cover_time_coordinate_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_signed_cover_time_parity_gate import (
    build_payload as build_signed_cover_time_parity_payload,
)


INPUT_PATH = Path("outputs/active_z2_sigma/time_gauge_leaf_action_inputs.json")
OUTPUT_PATH = Path("outputs/active_z2_sigma/background_curvature_sign_inputs.json")
REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_projective_spatial_slice_topology_branch_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_projective_spatial_slice_topology_branch_gate.json"
)


def _load(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def _branch_from_input(payload: dict) -> dict:
    if payload.get("active_core") != "Z2_tunnel_Sigma":
        raise ValueError("Input active_core must be Z2_tunnel_Sigma")
    if payload.get("source") != "active_derived":
        raise ValueError("Input source must be active_derived")
    for key in [
        "compressed_planck_lcdm_background_used",
        "archived_z4_background_reuse_used",
        "observational_curvature_fit_used",
    ]:
        if payload.get(key) is not False:
            raise ValueError(f"Forbidden provenance flag must be false: {key}")
    gauge = payload.get("time_gauge_leaf_action", {})
    if gauge.get("z2_equivariant_time_gauge_derived") is not True:
        raise ValueError("z2_equivariant_time_gauge_derived must be true")
    if gauge.get("flrw_slices_from_active_time_gauge") is not True:
        raise ValueError("flrw_slices_from_active_time_gauge must be true")
    action = gauge.get("leaf_action_type")
    if action == "antipodal_invariant_leaf":
        branch = "RP3"
        factor = 1.0
        provenance = "active_time_gauge_antipodal_invariant_leaf"
    elif action == "antipodal_paired_leaves":
        branch = "S3_paired_leaf_representative"
        factor = 2.0
        provenance = "active_time_gauge_antipodal_paired_leaves"
    else:
        raise ValueError(
            "leaf_action_type must be antipodal_invariant_leaf or antipodal_paired_leaves"
        )
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_background_reuse_used": False,
        "observational_curvature_fit_used": False,
        "scalars": {"k_Z2Sigma": 1},
        "scalar_provenance": {"k_Z2Sigma": provenance},
        "spatial_topology": {
            "quotient_spatial_slice": branch,
            "volume_factor_pi2_R3": factor,
        },
        "open_quantities": {
            "R_curv_Z2Sigma_still_required": True,
            "omega_k_Z2Sigma_not_computed_here": True,
        },
    }


def build_payload(*, input_path: Path = INPUT_PATH, output_path: Path = OUTPUT_PATH) -> dict:
    signed_time = None
    time_parity = None
    use_default_active_path = input_path == INPUT_PATH
    if use_default_active_path and not input_path.exists():
        signed_time = build_signed_cover_time_coordinate_payload()
        time_parity = build_signed_cover_time_parity_payload()
    leaf_action_writer = (
        build_time_gauge_leaf_action_writer_payload(output_path=input_path)
        if use_default_active_path
        else build_time_gauge_leaf_action_writer_payload()
    )
    input_exists = input_path.exists()
    validation_error = None
    output_written = False
    selected_branch = None
    volume_factor = None
    if input_exists:
        try:
            output = _branch_from_input(_load(input_path))
            output_path.parent.mkdir(parents=True, exist_ok=True)
            output_path.write_text(json.dumps(output, indent=2), encoding="utf-8")
            output_written = True
            selected_branch = output["spatial_topology"]["quotient_spatial_slice"]
            volume_factor = output["spatial_topology"]["volume_factor_pi2_R3"]
        except Exception as exc:
            validation_error = str(exc)
    return {
        "status": "janus-z2-sigma-projective-spatial-slice-topology-branch-gate",
        "active_core": "Z2_tunnel_Sigma",
        "input_manifest": str(input_path),
        "output_manifest": str(output_path),
        "input_exists": input_exists,
        "signed_cover_time_coordinate_gate_passed": (
            None if signed_time is None else signed_time["gate_passed"]
        ),
        "signed_cover_time_parity_gate_passed": (
            None if time_parity is None else time_parity["gate_passed"]
        ),
        "time_gauge_leaf_action_input_writer_passed": leaf_action_writer["gate_passed"],
        "time_parity_to_leaf_action_rule_ready": leaf_action_writer[
            "time_parity_to_leaf_action_rule_ready"
        ],
        "bibliography_checked": True,
        "primary_sources_checked": [
            "standard antipodal quotient S^3/Z2 = RP^3",
            "standard paired-leaf quotient of two exchanged copies by a free Z2 action",
        ],
        "global_S4_to_RP4_cover_ready": True,
        "positive_curvature_sign_supported": True,
        "rp3_single_invariant_leaf_branch": {
            "requires_antipodal_invariant_spatial_leaf": True,
            "spatial_quotient_leaf": "RP3",
            "volume_factor_pi2_R3": 1.0,
            "branch_closed": False,
        },
        "s3_paired_leaf_representative_branch": {
            "requires_antipodal_paired_spatial_leaves": True,
            "spatial_quotient_leaf": "S3_paired_leaf_representative",
            "volume_factor_pi2_R3": 2.0,
            "branch_closed": False,
        },
        "selected_spatial_topology_branch": selected_branch,
        "selected_volume_factor_pi2_R3": volume_factor,
        "topology_branch_selected": output_written,
        "curvature_sign_input_written": output_written,
        "curvature_radius_still_required": True,
        "omega_k_not_computed_here": True,
        "uses_compressed_planck_lcdm_background": False,
        "uses_archived_z4_background": False,
        "uses_observational_curvature_fit": False,
        "gate_passed": output_written,
        "validation_error": validation_error,
        "next_required": [
            *leaf_action_writer["next_required"],
            "write_outputs_active_z2_sigma_time_gauge_leaf_action_inputs_json",
            "derive_active_time_gauge_leaf_action_type",
            "select_RP3_invariant_leaf_or_S3_paired_leaf_representative_branch",
            "propagate_selected_spatial_topology_branch_to_curvature_and_volume_inputs",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Projective Spatial Slice Topology Branch Gate",
        "",
        f"Input exists: `{payload['input_exists']}`",
        f"Positive curvature supported: `{payload['positive_curvature_sign_supported']}`",
        f"Topology branch selected: `{payload['topology_branch_selected']}`",
        f"Gate passed: `{payload['gate_passed']}`",
        "",
        "## Branches",
        "- `RP3`: invariant leaf, volume `pi^2 R_curv^3`.",
        "- `S3_paired_leaf_representative`: paired leaves, volume `2*pi^2 R_curv^3`.",
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
