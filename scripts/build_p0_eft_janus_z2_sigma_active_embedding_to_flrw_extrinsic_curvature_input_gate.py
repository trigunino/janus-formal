from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from janus_lab.z2_sigma_embedding_geometry_manifest import (
    OPTIONAL_FLRW_EXTRINSIC_CURVATURE_FIELDS,
    REQUIRED_EMBEDDING_GEOMETRY_FIELDS,
    load_active_z2sigma_embedding_geometry_manifest,
    validate_optional_flrw_extrinsic_curvature_fields,
)
from scripts.build_p0_eft_janus_z2_sigma_active_tunnel_embedding_of_a_gate import (
    build_payload as build_active_tunnel_embedding_payload,
)


INPUT_PATH = Path("outputs/active_z2_sigma/active_tunnel_embedding_geometry_inputs.json")
OUTPUT_PATH = Path("outputs/active_z2_sigma/flrw_extrinsic_curvature_grid_inputs.json")
REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_active_embedding_to_flrw_extrinsic_curvature_input_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_active_embedding_to_flrw_extrinsic_curvature_input_gate.json"
)

REQUIRED_FIELDS = REQUIRED_EMBEDDING_GEOMETRY_FIELDS

def _path_status(path: Path) -> dict:
    exists = path.exists()
    missing_fields: list[str] = []
    missing_k_fields: list[str] = []
    validation_error = None
    payload = None
    if exists:
        try:
            payload = load_active_z2sigma_embedding_geometry_manifest(path)
            missing_fields = [field for field in REQUIRED_FIELDS if field not in payload]
            missing_k_fields = validate_optional_flrw_extrinsic_curvature_fields(payload)
        except Exception as exc:
            validation_error = str(exc)
    return {
        "path": str(path),
        "exists": exists,
        "missing_fields": missing_fields,
        "missing_k_fields": missing_k_fields,
        "validation_error": validation_error,
        "payload": payload,
    }


def build_payload(*, input_path: Path = INPUT_PATH, output_path: Path = OUTPUT_PATH) -> dict:
    embedding = build_active_tunnel_embedding_payload()
    manifest = _path_status(input_path)
    embedding_derived = embedding["derived"]
    embedding_missing = [
        key for key, ready in embedding_derived.items() if not ready
    ]
    manifest_blocks = (
        ([] if manifest["exists"] else ["active_tunnel_embedding_geometry_inputs_manifest"])
        + manifest["missing_fields"]
        + manifest["missing_k_fields"]
    )
    can_write = (
        manifest["exists"]
        and not manifest["missing_fields"]
        and not manifest["missing_k_fields"]
        and manifest["validation_error"] is None
    )
    if can_write:
        source = manifest["payload"]
        built = {
            "active_core": "Z2_tunnel_Sigma",
            "source": "active_derived",
            "compressed_planck_lcdm_background_used": False,
            "archived_z4_reuse_used": False,
            "phenomenological_holst_bao_scan_used": False,
            "a_grid": source["a_grid"],
            "K_s_plus_Z2Sigma": source["K_s_plus_Z2Sigma"],
            "K_s_minus_Z2Sigma": source["K_s_minus_Z2Sigma"],
            "K_tau_plus_Z2Sigma": source["K_tau_plus_Z2Sigma"],
            "K_tau_minus_Z2Sigma": source["K_tau_minus_Z2Sigma"],
            "z2_orientation_sign": source["z2_orientation_sign"],
            "K_provenance": source["K_provenance"],
        }
        output_path.parent.mkdir(parents=True, exist_ok=True)
        output_path.write_text(json.dumps(built, indent=2), encoding="utf-8")
    primary_blocker = (
        "none"
        if can_write
        else embedding.get("primary_blocker")
        or "active_embedding_and_unit_normals"
    )
    return {
        "status": "janus-z2-sigma-active-embedding-to-flrw-extrinsic-curvature-input-gate",
        "active_core": "Z2_tunnel_Sigma",
        "input_manifest": manifest,
        "output_manifest": str(output_path),
        "adapter_declared": True,
        "required_fields": REQUIRED_FIELDS,
        "optional_k_fields": OPTIONAL_FLRW_EXTRINSIC_CURVATURE_FIELDS,
        "active_tunnel_embedding_of_a_closure_ready": embedding[
            "active_tunnel_embedding_of_a_closure_ready"
        ],
        "active_embedding_derived": embedding["derived"],
        "upstream_frontiers": {
            "active_tunnel_embedding_of_a": {
                "gate": embedding["status"],
                "closure_ready": embedding["active_tunnel_embedding_of_a_closure_ready"],
                "derived": embedding_derived,
                "next_required": embedding["next_required"],
                "bibliography_result": embedding["bibliography_result"],
                "primary_blocker": embedding.get("primary_blocker"),
            },
            "embedding_geometry_manifest": {
                "path": str(input_path),
                "exists": manifest["exists"],
                "missing_fields": manifest["missing_fields"],
                "missing_k_fields": manifest["missing_k_fields"],
                "required_fields": REQUIRED_FIELDS,
            },
        },
        "nearest_embedding_to_flrw_K_frontier": {
            "blocks": [] if can_write else embedding_missing + manifest_blocks,
            "legacy_static_embedding_blocks": embedding_missing,
            "diagnostic_only": True,
        },
        "would_write_flrw_extrinsic_curvature_grid_inputs": can_write,
        "gate_passed": can_write,
        "primary_blocker": primary_blocker,
        "blocker": None
        if can_write
        else "active embedding manifest must include derived K_s/K_tau plus/minus reductions",
        "next_required": [
            "derive_regular_throat_radius_RSigma_of_a",
            "derive_X_plus_of_a_and_X_minus_of_a",
            "derive_tangent_frames_and_unit_normals",
            "derive_K_s_tau_plus_minus_of_a",
            "then_write_flrw_extrinsic_curvature_grid_inputs_json",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Active Embedding To FLRW Extrinsic Curvature Input Gate",
        "",
        f"Adapter declared: `{payload['adapter_declared']}`",
        f"Embedding closure ready: `{payload['active_tunnel_embedding_of_a_closure_ready']}`",
        f"Input exists: `{payload['input_manifest']['exists']}`",
        f"Would write K-grid inputs: `{payload['would_write_flrw_extrinsic_curvature_grid_inputs']}`",
        f"Gate passed: `{payload['gate_passed']}`",
        "",
        "## Next Required",
    ]
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
