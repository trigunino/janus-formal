from __future__ import annotations

import json
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from scripts.build_p0_eft_janus_z2_sigma_projective_gluing_normal_orientation_sign_gate import (
    build_payload as build_normal_orientation_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_spinor_boundary_projection_map_gate import (
    build_payload as build_spinor_projection_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_dirac_current_parity_from_spinor_intertwiner_gate import (
    build_payload as build_current_parity_payload,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_dirac_normal_current_z2_cancellation_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_dirac_normal_current_z2_cancellation_gate.json")


def build_payload() -> dict:
    orientation = build_normal_orientation_payload()
    spinor_projection = build_spinor_projection_payload()
    current_parity = build_current_parity_payload()
    normal_reversal_ready = orientation["projective_gluing_normal_orientation_sign_ready"]
    current_parity_derived = current_parity["dirac_current_z2_parity_ready"]
    projected_current_sign_fixed = False
    cancellation_ready = (
        normal_reversal_ready
        and current_parity_derived
        and projected_current_sign_fixed
        and spinor_projection["spinor_boundary_projection_map_ready"]
    )
    return {
        "status": "janus-z2-sigma-dirac-normal-current-z2-cancellation-gate",
        "active_core": "Z2_tunnel_Sigma",
        "declared": {
            "Z2_sheet_exchange_declared": True,
            "normal_reversal_imported": True,
            "Dirac_current_transport_declared": True,
            "projected_normal_current_formula_declared": True,
            "no_MIT_boundary_assumption_required_for_this_route": True,
            "observational_fit_forbidden": True,
        },
        "closure": {
            "Z2_normal_reversal_ready": normal_reversal_ready,
            "spinor_projection_map_ready": spinor_projection["spinor_boundary_projection_map_ready"],
            "conditional_current_parity_algebra_ready": current_parity[
                "conditional_current_parity_algebra_ready"
            ],
            "Dirac_current_Z2_parity_derived": current_parity_derived,
            "projected_current_orientation_sign_fixed": projected_current_sign_fixed,
            "Z2_projected_normal_current_zero_derived": cancellation_ready,
        },
        "formulas": {
            "normal_reversal": "n_- = - tau_Z2_* n_+",
            "current_parity_needed": "J_- = sigma_J tau_Z2_* J_+",
            "normal_current_relation": "J_n^- = - sigma_J J_n^+",
            "cancellation_condition": "J_n^Z2Sigma = J_n^+ + eps_current J_n^- = 0",
        },
        "upstream_frontiers": {
            "current_parity_from_spinor_intertwiner": {
                "gate": current_parity["status"],
                "ready": current_parity["dirac_current_z2_parity_ready"],
                "primary_blocker": current_parity["primary_blocker"],
                "equivariance_route_blockers": current_parity.get(
                    "equivariance_route_blockers", []
                ),
                "conditional_algebra_ready": current_parity[
                    "conditional_current_parity_algebra_ready"
                ],
            },
        },
        "interpretation": (
            "This is the Janus/Z2 alternative to a reflecting MIT boundary: the "
            "normal current cancels by sheet parity. It is not closed until the "
            "Dirac current parity and projected-current sign are derived from the "
            "active spinor projection."
        ),
        "dirac_normal_current_z2_cancellation_ready": cancellation_ready,
        "gate_passed": cancellation_ready,
        "primary_blocker": "none"
        if cancellation_ready
        else (
            current_parity["primary_blocker"]
            if normal_reversal_ready
            else "Z2_normal_reversal"
        ),
        "route_blockers": current_parity.get("equivariance_route_blockers", [])
        if normal_reversal_ready and not cancellation_ready
        else [],
        "next_required": []
        if cancellation_ready
        else [
            "derive_Dirac_current_Z2_parity_from_spinor_projection",
            "fix_projected_current_orientation_sign_from_action",
            "prove_J_n_Z2Sigma_equals_zero_or_reject_cancellation_route",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Dirac Normal Current Z2 Cancellation Gate",
        "",
        f"Ready: `{payload['dirac_normal_current_z2_cancellation_ready']}`",
        f"Primary blocker: `{payload['primary_blocker']}`",
        "",
        payload["interpretation"],
    ]
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
