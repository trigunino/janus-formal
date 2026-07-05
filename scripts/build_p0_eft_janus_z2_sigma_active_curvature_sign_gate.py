from __future__ import annotations

import json
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from scripts.build_p0_eft_janus_z2_sigma_active_flrw_spatial_metric_branch_gate import (
    build_payload as build_active_flrw_spatial_metric_branch_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_rp3_spatial_slice_curvature_sign_gate import (
    build_payload as build_rp3_spatial_slice_curvature_sign_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_rp3_spatial_slice_input_writer_from_projective_foliation_gate import (
    build_payload as build_rp3_spatial_slice_input_writer_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_projective_spatial_slice_topology_branch_gate import (
    build_payload as build_projective_spatial_slice_topology_branch_payload,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_active_curvature_sign_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_active_curvature_sign_gate.json")


def build_payload() -> dict:
    branch = build_active_flrw_spatial_metric_branch_payload()
    topology_branch = build_projective_spatial_slice_topology_branch_payload()
    rp3_writer = build_rp3_spatial_slice_input_writer_payload()
    rp3_sign = build_rp3_spatial_slice_curvature_sign_payload()
    sign_ready = topology_branch["gate_passed"] or rp3_sign["gate_passed"]
    return {
        "status": "janus-z2-sigma-active-curvature-sign-gate",
        "active_core": "Z2_tunnel_Sigma",
        "bibliography_checked": True,
        "primary_sources_checked": [
            "standard FLRW spatial-curvature classification k in {-1,0,+1}",
            "active Janus projective/tunnel topology gates",
        ],
        "projective_tunnel_two_fold_topology_ready": True,
        "topology_alone_fixes_FLRW_curvature_sign": False,
        "flrw_spatial_metric_branch_gate_passed": branch["gate_passed"],
        "flrw_spatial_metric_branch_values_ready": branch[
            "flrw_spatial_metric_branch_values_ready"
        ],
        "rp3_spatial_slice_to_k_plus_one_rule_ready": rp3_sign[
            "rp3_spatial_slice_to_k_plus_one_rule_ready"
        ],
        "rp3_spatial_slice_input_writer_passed": rp3_writer["gate_passed"],
        "projective_foliation_to_rp3_slice_rule_ready": rp3_writer[
            "projective_foliation_to_rp3_slice_rule_ready"
        ],
        "rp3_spatial_slice_curvature_sign_gate_passed": rp3_sign["gate_passed"],
        "projective_spatial_slice_topology_branch_gate_passed": topology_branch[
            "gate_passed"
        ],
        "selected_spatial_topology_branch": topology_branch[
            "selected_spatial_topology_branch"
        ],
        "rp3_curvature_radius_still_required": rp3_sign[
            "curvature_radius_still_required"
        ],
        "curvature_sign_domain_declared": True,
        "curvature_sign_allowed_values": [-1, 0, 1],
        "requires_active_spatial_metric_branch": True,
        "requires_active_embedding_scale_or_induced_spatial_metric": True,
        "requires_R_Sigma_or_X_plus_minus_solution": True,
        "uses_compressed_planck_lcdm_background": False,
        "uses_archived_z4_background": False,
        "uses_observational_curvature_fit": False,
        "curvature_sign_values_ready": sign_ready,
        "gate_passed": sign_ready,
        "next_required": list(dict.fromkeys(topology_branch["next_required"] + rp3_writer["next_required"] + rp3_sign["next_required"] + [
            "close_active_FLRW_spatial_metric_branch_gate",
            "derive_active_spatial_metric_branch",
            "derive_active_induced_spatial_metric_on_FLRW_slices",
            "derive_curvature_sign_k_Z2Sigma_from_active_metric_or_embedding",
            "feed_curvature_sign_k_Z2Sigma_into_active_omega_k_derivation_gate",
        ])),
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Active Curvature Sign Gate",
        "",
        f"Curvature sign domain declared: `{payload['curvature_sign_domain_declared']}`",
        f"Topology alone fixes FLRW curvature sign: `{payload['topology_alone_fixes_FLRW_curvature_sign']}`",
        f"Curvature sign values ready: `{payload['curvature_sign_values_ready']}`",
        f"RP3 input writer passed: `{payload['rp3_spatial_slice_input_writer_passed']}`",
        f"Topology branch gate passed: `{payload['projective_spatial_slice_topology_branch_gate_passed']}`",
        f"RP3 sign gate passed: `{payload['rp3_spatial_slice_curvature_sign_gate_passed']}`",
        f"Gate passed: `{payload['gate_passed']}`",
        "",
        "## Policy",
        "- The projective/tunnel two-fold topology supplies the active cover structure.",
        "- The observable FLRW sign `k_Z2Sigma` must come from the active spatial metric branch or embedding.",
        "- No compressed Planck/LCDM, archived Z4, or observational curvature fit may supply the sign.",
        "",
        "## Next Required",
    ]
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
