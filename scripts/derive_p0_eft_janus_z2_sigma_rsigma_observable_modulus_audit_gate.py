from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.derive_p0_eft_janus_z2_sigma_rsigma_modulus_fixing_principles_gate import (
    build_payload as build_modulus_payload,
)


REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_rsigma_observable_modulus_audit_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_rsigma_observable_modulus_audit_gate.json"
)


def build_payload() -> dict:
    modulus = build_modulus_payload()
    sectors = {
        "projective_topology": {
            "uses_R_Sigma": False,
            "reason": "S4/RP4 cover, Z2 parity, and tunnel existence are dimensionless/topological.",
        },
        "local_radial_balance_after_sqrt_Rh_counterterm": {
            "uses_R_Sigma": True,
            "reason": "the equation is flat in R_Sigma: it permits any positive radius but predicts none.",
        },
        "active_embedding_and_collar_geometry": {
            "uses_R_Sigma": True,
            "reason": "X_+/-, normals, K_ab, and collar stencils are functions of R_Sigma(a).",
        },
        "dimensional_background_H0_Rcurv": {
            "uses_R_Sigma": True,
            "reason": "current H0/R_curv writers derive their scale from the R_Sigma certificate.",
        },
        "official_dimensional_BAO": {
            "uses_R_Sigma": True,
            "reason": "official BAO needs dimensional H(z), r_d, and curvature scale provenance.",
        },
        "scale_free_BAO_formulation": {
            "uses_R_Sigma": False,
            "reason": "in principle it needs only E(z), c_s/c, Gamma_drag/H0, omega_k, and z_d.",
            "current_pipeline_still_blocked": True,
            "current_blocker": "active dimensionless inputs and counterterm reduction are not fully materialized",
        },
    }
    full_observable_cancellation = not any(
        item["uses_R_Sigma"]
        for name, item in sectors.items()
        if name not in {"projective_topology", "scale_free_BAO_formulation"}
    )
    return {
        "status": "janus-z2-sigma-rsigma-observable-modulus-audit-gate",
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_dependency_audit",
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_reuse_used": False,
        "archived_z4_background_reuse_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "observational_H0_fit_used": False,
        "observational_curvature_fit_used": False,
        "fitted_counterterm_coefficient_used": False,
        "R_Sigma_modulus_open": modulus["R_Sigma_modulus_open"],
        "sectors": sectors,
        "full_observable_RSigma_cancellation_proved": full_observable_cancellation,
        "flat_modulus_certificate_allowed_for_full_pipeline": False,
        "flat_modulus_usable_for_projective_topology_only": True,
        "scale_free_branch_can_be_pursued_without_extension": True,
        "official_dimensional_branch_requires_radius_or_scale_input": True,
        "gate_passed": True,
        "primary_blocker": "full_pipeline_still_depends_on_RSigma",
        "next_required": [
            "do not add C R[h] extension",
            "pursue scale-free branch only with explicit R_Sigma-free inputs",
            "or keep full dimensional pipeline blocked until R_Sigma modulus is fixed",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma R_Sigma Observable Modulus Audit Gate",
        "",
        f"Full observable cancellation proved: `{payload['full_observable_RSigma_cancellation_proved']}`",
        f"Scale-free branch can continue: `{payload['scale_free_branch_can_be_pursued_without_extension']}`",
        f"Primary blocker: `{payload['primary_blocker']}`",
        "",
        "## Sectors",
    ]
    for name, item in payload["sectors"].items():
        lines.append(f"- `{name}` uses_R=`{item['uses_R_Sigma']}`: {item['reason']}")
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
