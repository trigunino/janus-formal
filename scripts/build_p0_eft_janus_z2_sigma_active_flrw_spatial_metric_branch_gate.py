from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_active_flrw_spatial_metric_branch_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_active_flrw_spatial_metric_branch_gate.json")


def build_payload() -> dict:
    return {
        "status": "janus-z2-sigma-active-flrw-spatial-metric-branch-gate",
        "active_core": "Z2_tunnel_Sigma",
        "bibliography_checked": True,
        "primary_sources_checked": [
            "standard FLRW constant-curvature spatial metric classification",
            "active Janus Z2/Sigma tunnel embedding gates",
        ],
        "projective_tunnel_two_fold_topology_ready": True,
        "topology_alone_fixes_spatial_metric_branch": False,
        "flrw_spatial_metric_contract_declared": True,
        "curvature_sign_domain_declared": True,
        "curvature_sign_allowed_values": [-1, 0, 1],
        "curvature_radius_symbol_declared": True,
        "spatial_scalar_curvature_relation_declared": True,
        "spatial_scalar_curvature_relation": "R3_Z2Sigma = 6*k_Z2Sigma/R_curv_Z2Sigma^2",
        "requires_active_tunnel_embedding_X_plus_minus_of_a": True,
        "requires_active_induced_spatial_metric_on_FLRW_slices": True,
        "requires_R_Sigma_or_embedding_scale": True,
        "uses_compressed_planck_lcdm_background": False,
        "uses_archived_z4_background": False,
        "uses_observational_curvature_fit": False,
        "flrw_spatial_metric_branch_values_ready": False,
        "curvature_sign_values_ready": False,
        "curvature_radius_values_ready": False,
        "gate_passed": False,
        "next_required": [
            "derive_X_plus_minus_of_a_from_active_tunnel_embedding",
            "derive_induced_spatial_metric_on_active_FLRW_slices",
            "classify_constant_curvature_branch_k_Z2Sigma",
            "derive_R_curv_Z2Sigma_from_active_embedding_scale",
            "feed_k_Z2Sigma_and_R_curv_Z2Sigma_to_active_curvature_sign_and_omega_k_gates",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Active FLRW Spatial Metric Branch Gate",
        "",
        f"Metric branch contract declared: `{payload['flrw_spatial_metric_contract_declared']}`",
        f"Topology alone fixes branch: `{payload['topology_alone_fixes_spatial_metric_branch']}`",
        f"Branch values ready: `{payload['flrw_spatial_metric_branch_values_ready']}`",
        f"Gate passed: `{payload['gate_passed']}`",
        "",
        "## Curvature Relation",
        f"`{payload['spatial_scalar_curvature_relation']}`",
        "",
        "## Next Required",
    ]
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
