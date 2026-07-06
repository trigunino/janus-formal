from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.derive_p0_eft_janus_z2_sigma_sqrt_intrinsic_curvature_counterterm_gate import (
    build_payload as build_sqrt_counterterm_payload,
)
from scripts.derive_p0_eft_janus_z2_sigma_core_action_radius_stationarity_gate import (
    build_payload as build_core_action_payload,
)
from scripts.derive_p0_eft_janus_z2_sigma_existing_action_core_ratio_audit_gate import (
    build_payload as build_existing_action_ratio_payload,
)
from scripts.derive_p0_eft_janus_z2_sigma_surface_intrinsic_curvature_policy_gate import (
    build_payload as build_intrinsic_curvature_policy_payload,
)
from scripts.derive_p0_eft_janus_z2_sigma_global_regular_tunnel_radius_selection_gate import (
    build_payload as build_global_regular_tunnel_payload,
)


REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_rsigma_modulus_fixing_principles_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_rsigma_modulus_fixing_principles_gate.json"
)


def build_payload() -> dict:
    sqrt_ct = build_sqrt_counterterm_payload()
    core_action = build_core_action_payload()
    existing_action = build_existing_action_ratio_payload()
    intrinsic_policy = build_intrinsic_curvature_policy_payload()
    global_regular = build_global_regular_tunnel_payload()
    principles = {
        "projective_Z2_topology": {
            "fixes": "two-fold cover and orientation reversal",
            "fixes_R_Sigma": False,
            "reason": "topology supplies dimensionless cover data, not a throat length scale",
        },
        "smooth_tubular_replacement": {
            "fixes": "existence of a resolved throat Sigma",
            "fixes_R_Sigma": False,
            "reason": "a tubular neighbourhood has a radius parameter unless a metric/action fixes it",
        },
        "embedding_gauge": {
            "fixes": "time/radial embedding derivatives after R_Sigma(a)",
            "fixes_R_Sigma": False,
            "reason": "gauge equations are conditional on the radius law",
        },
        "sqrt_intrinsic_curvature_counterterm": {
            "fixes": "local cancellation of the round Cartan-GHY radial block",
            "fixes_R_Sigma": sqrt_ct["closure_result"]["R_Sigma_of_a_fixed"],
            "reason": "its Euler block is flat in R_Sigma after cancellation",
        },
        "point_collapse_limit": {
            "fixes": "singular endpoint R_Sigma -> 0 if separately proved",
            "fixes_R_Sigma": False,
            "reason": "not compatible with the active smooth Sigma pipeline without a defect-limit proof",
        },
        "core_tension_plus_intrinsic_R": {
            "fixes": "finite radius if B and C are derived with opposite signs",
            "fixes_R_Sigma": core_action["closure_result"][
                "R_Sigma_of_a_fixed_without_extra_coefficients"
            ],
            "reason": "stationarity gives R^2=-2C/B, but C/B is not yet derived",
        },
        "existing_formal_action": {
            "fixes": "membrane tension B but not intrinsic surface curvature C",
            "fixes_R_Sigma": existing_action["core_radius_stationarity"][
                "existing_action_derives_C_over_B"
            ],
            "reason": "formal candidate action currently lacks Sigma-localized C R[h]",
        },
        "surface_intrinsic_curvature_policy": {
            "fixes": "would fix finite R only after C/B is derived or explicitly adopted",
            "fixes_R_Sigma": False,
            "reason": intrinsic_policy["primary_blocker"],
        },
        "global_regular_tunnel_selection": {
            "fixes": "dimensionless throat/collar ratio if F_reg(lambda_Sigma)=0 is computed and non-flat",
            "fixes_R_Sigma": global_regular["radius_selection_ready"],
            "reason": global_regular["primary_blocker"],
        },
    }
    fixed_by_known_internal_principle = any(
        item["fixes_R_Sigma"] for item in principles.values()
    )
    return {
        "status": "janus-z2-sigma-rsigma-modulus-fixing-principles-gate",
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_symbolic_audit",
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_reuse_used": False,
        "archived_z4_background_reuse_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "observational_H0_fit_used": False,
        "observational_curvature_fit_used": False,
        "fitted_counterterm_coefficient_used": False,
        "principles": principles,
        "fixed_by_known_internal_principle": fixed_by_known_internal_principle,
        "R_Sigma_modulus_open": not fixed_by_known_internal_principle,
        "gate_passed": True,
        "primary_blocker": "R_Sigma_modulus_open"
        if not fixed_by_known_internal_principle
        else "none",
        "next_physical_inputs": [
            "derive the throat-core ratio C/B in L_core=A sqrt(R[h])+B+C R[h]",
            "or derive a regularity/quantization condition that fixes the tubular radius",
            "compute the global regular tunnel functional F_reg(lambda_Sigma)",
            "or explicitly downgrade R_Sigma to a gauge modulus and remove it from observable certificates",
        ]
        if not fixed_by_known_internal_principle
        else [],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma R_Sigma Modulus Fixing Principles Gate",
        "",
        f"R_Sigma modulus open: `{payload['R_Sigma_modulus_open']}`",
        f"Primary blocker: `{payload['primary_blocker']}`",
        "",
        "## Principles",
    ]
    for name, item in payload["principles"].items():
        lines.append(f"- `{name}` fixes_R=`{item['fixes_R_Sigma']}`: {item['reason']}")
    lines.extend(["", "## Next Physical Inputs"])
    lines.extend(f"- `{item}`" for item in payload["next_physical_inputs"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
