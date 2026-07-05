from __future__ import annotations

import json
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from scripts.build_p0_eft_janus_z2_sigma_local_pin_reflection_intertwiner_gate import (
    build_payload as build_local_intertwiner_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_resolved_tunnel_pin_lift_gate import (
    build_payload as build_resolved_tunnel_pin_lift_payload,
)


REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_spinor_quotient_descent_equivariance_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_spinor_quotient_descent_equivariance_gate.json"
)


def build_payload() -> dict:
    pin_lift = build_resolved_tunnel_pin_lift_payload()
    local_intertwiner = build_local_intertwiner_payload()
    declared = {
        "quotient_section_descent_bibliography_checked": True,
        "double_cover_deck_action_declared": True,
        "equivariant_bundle_descent_theorem_imported": True,
        "pinor_double_cover_sheet_exchange_bibliography_checked": True,
        "local_U_Z2_sigma_imported": local_intertwiner["local_pin_reflection_intertwiner_ready"],
        "observational_fit_forbidden": True,
    }
    closure = {
        "resolved_tunnel_Pin_lift_ready": pin_lift["resolved_tunnel_pin_lift_ready"],
        "deck_action_lifted_to_spinor_bundle": pin_lift["resolved_tunnel_pin_lift_ready"],
        "physical_spinor_declared_as_quotient_section": False,
        "quotient_section_lifts_equivariantly": False,
        "physical_spinor_equivariance_psi_minus_equals_U_Z2_psi_plus": False,
    }
    ready = all(declared.values()) and all(closure.values())
    return {
        "status": "janus-z2-sigma-spinor-quotient-descent-equivariance-gate",
        "active_core": "Z2_tunnel_Sigma",
        "source_links": [
            "https://ncatlab.org/nlab/show/equivariant%2Bbundle",
            "https://arxiv.org/pdf/0907.4334",
        ],
        "bibliography_result": (
            "Equivariant bundle descent gives the right mathematical route: a spinor "
            "field defined on the Janus quotient lifts to a deck-equivariant spinor "
            "on the double cover. For pinors on a non-orientable quotient, the active "
            "resolved-tunnel Pin lift and its sheet-exchange action must still be built."
        ),
        "declared": declared,
        "closure": closure,
        "route": {
            "quotient_field": "psi_Q is a section of the resolved Janus quotient spinor bundle",
            "lift": "pi^* psi_Q = (psi_+, psi_-) on the two-fold cover",
            "equivariance": "psi_-|_Sigma = U_Z2^Sigma psi_+|_Sigma",
            "local_intertwiner": "U_Z2^Sigma := B_n",
        },
        "forbidden": [
            "independent plus/minus spinors without quotient descent",
            "free spinor phase",
            "legacy Z4 monodromy",
            "observational fit for current parity",
        ],
        "physical_spinor_equivariance_from_quotient_descent_ready": ready,
        "gate_passed": ready,
        "primary_blocker": "none"
        if ready
        else "resolved_tunnel_Pin_lift_for_spinor_descent",
        "next_required": []
        if ready
        else [
            "close_resolved_tunnel_Pin_lift_gate",
            "derive_deck_action_lift_on_spinor_bundle",
            "declare_physical_spinor_as_quotient_section",
            "then_promote_psi_minus_equals_U_Z2_psi_plus",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Spinor Quotient Descent Equivariance Gate",
        "",
        f"Ready: `{payload['physical_spinor_equivariance_from_quotient_descent_ready']}`",
        f"Primary blocker: `{payload['primary_blocker']}`",
        "",
        payload["bibliography_result"],
    ]
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
