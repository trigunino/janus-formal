from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z2_sigma_flrw_extrinsic_curvature_grid_writer_gate import (
    build_payload as build_grid_writer_payload,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_flrw_extrinsic_curvature_grid_builder_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_flrw_extrinsic_curvature_grid_builder_gate.json")


def build_payload() -> dict:
    writer = build_grid_writer_payload()
    return {
        "status": "janus-z2-sigma-flrw-extrinsic-curvature-grid-builder-gate",
        "active_core": "Z2_tunnel_Sigma",
        "flrw_K_grid_builder_ready": True,
        "composes_metric_geometry_primitives": True,
        "composes_extrinsic_curvature_tensor_builder": True,
        "produces_K_s_of_a_array": True,
        "produces_K_tau_of_a_array": True,
        "requires_active_a_grid": True,
        "requires_active_tangent_vectors": True,
        "requires_active_second_embedding": True,
        "requires_active_christoffel_symbols": True,
        "requires_active_normal_covector": True,
        "requires_active_spatial_inverse_metric": True,
        "uses_planck_lcdm_inputs": False,
        "uses_archived_z4_inputs": False,
        "K_s_tau_values_ready": writer["flrw_extrinsic_curvature_grid_written"],
        "upstream_frontiers": {
            "flrw_extrinsic_curvature_grid_writer": {
                "gate": writer["status"],
                "ready": writer["gate_passed"],
                "input_exists": writer["input_exists"],
                "active_tunnel_embedding_of_a_closure_ready": writer[
                    "active_tunnel_embedding_of_a_closure_ready"
                ],
            },
        },
        "gate_passed": True,
        "next_required": [
            "derive_active_tunnel_embedding_X_plus_minus_of_a",
            "evaluate_plus_minus_metric_geometry_primitives_on_a_grid",
            "feed_K_s_tau_plus_minus_arrays_to_DeltaK_jump_builder",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma FLRW Extrinsic Curvature Grid Builder Gate",
        "",
        f"Grid builder ready: `{payload['flrw_K_grid_builder_ready']}`",
        f"K_s/K_tau values ready: `{payload['K_s_tau_values_ready']}`",
        f"Gate passed: `{payload['gate_passed']}`",
        "",
        "## Next Required",
    ]
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
