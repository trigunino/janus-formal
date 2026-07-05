from __future__ import annotations

import json
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from scripts.build_p0_eft_janus_z2_sigma_active_curvature_sign_gate import (
    build_payload as build_active_curvature_sign_payload,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_active_omega_k_derivation_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_active_omega_k_derivation_gate.json")


def build_payload() -> dict:
    curvature_sign = build_active_curvature_sign_payload()
    return {
        "status": "janus-z2-sigma-active-omega-k-derivation-gate",
        "active_core": "Z2_tunnel_Sigma",
        "bibliography_checked": True,
        "primary_sources_checked": [
            "Hogg 1999 distance measures in cosmology, arXiv:astro-ph/9905116",
            "standard FLRW curvature convention Omega_k = -k c^2/(H0^2 R_curv^2)",
        ],
        "projective_tunnel_two_fold_topology_ready": True,
        "topology_alone_fixes_numeric_omega_k": False,
        "omega_k_formula_builder_ready": True,
        "omega_k_formula": "omega_k_Z2Sigma = -k_Z2Sigma * c^2 / (H0_Z2Sigma^2 R_curv_Z2Sigma^2)",
        "requires_active_H0_Z2Sigma": True,
        "requires_curvature_sign_k_Z2Sigma": True,
        "curvature_sign_gate_passed": curvature_sign["gate_passed"],
        "curvature_sign_values_ready": curvature_sign["curvature_sign_values_ready"],
        "topology_alone_fixes_FLRW_curvature_sign": curvature_sign[
            "topology_alone_fixes_FLRW_curvature_sign"
        ],
        "requires_active_FLRW_curvature_radius_or_embedding_scale": True,
        "requires_active_R_Sigma_or_embedding_solution": True,
        "uses_compressed_planck_lcdm_background": False,
        "uses_archived_z4_background": False,
        "uses_observational_H0_fit": False,
        "omega_k_Z2Sigma_values_ready": False,
        "background_curvature_normalization_inputs_ready": False,
        "gate_passed": False,
        "next_required": [
            "close_active_curvature_sign_gate",
            "derive_curvature_sign_k_Z2Sigma_from_active_FLRW_branch",
            "derive_active_FLRW_curvature_radius_or_embedding_scale",
            "solve_R_Sigma_of_a_or_embedding_scale_before_numeric_omega_k",
            "write_outputs_active_z2_sigma_background_curvature_normalization_inputs_json",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Active Omega_k Derivation Gate",
        "",
        f"Formula builder ready: `{payload['omega_k_formula_builder_ready']}`",
        f"Omega_k values ready: `{payload['omega_k_Z2Sigma_values_ready']}`",
        f"Gate passed: `{payload['gate_passed']}`",
        "",
        "## Formula",
        f"`{payload['omega_k_formula']}`",
        "",
        "## Next Required",
    ]
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
