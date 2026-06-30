from __future__ import annotations

from pathlib import Path
import json
import sys


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_projected_cuu_action_derivation_target import (
    build_payload as build_action_target,
)
from scripts.build_p0_cuu_inverse_map_integrability_target import (
    build_payload as build_inverse_integrability,
)
from scripts.build_p0_dust_monoflux_cuu_conditional_closure import (
    build_payload as build_dust_conditional,
)
from scripts.build_p0_pulled_dust_el_cuu_substitution_proof import (
    build_payload as build_substitution_proof,
)
from scripts.build_p0_same_phi_l_cuu_bridge import build_payload as build_same_phi_l_bridge


REPORT_PATH = Path("outputs/reports/p0_projected_cuu_action_pullback_bridge_ledger.md")
JSON_PATH = Path("outputs/reports/p0_projected_cuu_action_pullback_bridge_ledger.json")


def build_payload() -> dict:
    action = build_action_target()
    dust_conditional = build_dust_conditional()
    proof = build_substitution_proof()
    bridge = build_same_phi_l_bridge()
    inverse_integrability = build_inverse_integrability()
    bridge_rows = [
        {
            "id": "CUU-ACTION",
            "obligation": "pullback_dust_action",
            "required_identity": "write the pulled dust action with the same phi/L/B4vol variables",
            "current_anchor": "p0_projected_cuu_action_derivation_target",
            "closed": action["projected_cuu_identity_derived"],
        },
        {
            "id": "CUU-VAR",
            "obligation": "projected_el_variation",
            "required_identity": "h E_phi/E_L equals rho h C(u_to,u_to), not an imposed constraint",
            "current_anchor": "p0_pulled_dust_el_cuu_substitution_proof",
            "closed": bool(
                proof["projected_cuu_identity_proved"]
                and dust_conditional["action_derivation_supplied"]
            ),
        },
        {
            "id": "CUU-SAME",
            "obligation": "same_phi_l_map",
            "required_identity": "same phi/L used by dust pullback, L transport, and B4vol",
            "current_anchor": "p0_same_phi_l_cuu_bridge",
            "closed": bridge["same_phi_l_bridge_closed"],
        },
        {
            "id": "CUU-DYN",
            "obligation": "dynamic_phi_l_selection",
            "required_identity": "Janus action/source uniquely selects phi/L",
            "current_anchor": "p0_pulled_dust_el_cuu_substitution_proof",
            "closed": proof["dynamic_phi_l_selection_closed"],
        },
        {
            "id": "CUU-MIRROR",
            "obligation": "mirror_inverse",
            "required_identity": "plus and minus Cuu rows follow from one inverse phi/L pair",
            "current_anchor": "p0_cuu_inverse_map_integrability_target",
            "closed": inverse_integrability["mirror_inverse_closed"],
        },
        {
            "id": "CUU-INTEG",
            "obligation": "integrability",
            "required_identity": "curl/caustic obstruction absent on transported dust support",
            "current_anchor": "p0_cuu_inverse_map_integrability_target",
            "closed": inverse_integrability["integrability_closed"],
        },
    ]
    forbidden_operations = [
        "do not impose hE=rho hCuu as an axiom when action variation is missing",
        "do not use a different phi/L for Cuu than for B4vol and same-L transport",
        "do not promote single-cross dust bridge to full mirror closure",
        "do not extend to pressure/Pi without separate matter transport",
    ]
    return {
        "description": "Action/pullback bridge ledger for the projected Cuu force identity.",
        "status": "projected-cuu-action-pullback-bridge-ledger-open",
        "depends_on": [
            "p0_projected_cuu_action_derivation_target",
            "p0_pulled_dust_el_cuu_substitution_proof",
            "p0_same_phi_l_cuu_bridge",
            "p0_cuu_inverse_map_integrability_target",
        ],
        "bridge_rows": bridge_rows,
        "forbidden_operations": forbidden_operations,
        "dust_monoflux_cuu_conditional_available": dust_conditional["conditional_cuu_closure"],
        "dust_monoflux_action_derivation_supplied": dust_conditional["action_derivation_supplied"],
        "single_cross_dust_bridge_closed": bridge["single_cross_dust_cuu_force_closed"],
        "dynamic_phi_l_selection_closed": proof["dynamic_phi_l_selection_closed"],
        "inverse_c_relation_written": inverse_integrability["inverse_c_relation_written"],
        "jacobian_from_same_l_written": inverse_integrability["jacobian_from_same_l_written"],
        "mirror_consistency_closed": inverse_integrability["mirror_inverse_closed"],
        "projected_cuu_action_bridge_closed": all(row["closed"] for row in bridge_rows),
        "uses_observational_fit": False,
        "r_plus_closed": False,
        "r_minus_closed": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "The single-cross dust Cuu bridge is conditionally available, but the Janus "
            "action/pullback bridge is still open because dynamic phi/L, mirror, and integrability rows remain unclosed."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Projected Cuu Action/Pullback Bridge Ledger",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Dust monoflux Cuu conditional available: {payload['dust_monoflux_cuu_conditional_available']}",
        f"Dust monoflux action derivation supplied: {payload['dust_monoflux_action_derivation_supplied']}",
        f"Single-cross dust bridge closed: {payload['single_cross_dust_bridge_closed']}",
        f"Dynamic phi/L selection closed: {payload['dynamic_phi_l_selection_closed']}",
        f"Mirror consistency closed: {payload['mirror_consistency_closed']}",
        f"Projected Cuu action bridge closed: {payload['projected_cuu_action_bridge_closed']}",
        f"Uses observational fit: {payload['uses_observational_fit']}",
        f"R plus closed: {payload['r_plus_closed']}",
        f"R minus closed: {payload['r_minus_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Bridge Rows",
        "",
        "| id | obligation | anchor | closed | required identity |",
        "|---|---|---|---:|---|",
    ]
    for row in payload["bridge_rows"]:
        lines.append(
            f"| {row['id']} | {row['obligation']} | {row['current_anchor']} | "
            f"{row['closed']} | {row['required_identity']} |"
        )
    lines.extend(["", "## Forbidden Operations", ""])
    lines.extend(f"- {item}" for item in payload["forbidden_operations"])
    lines.extend(["", f"Verdict: {payload['verdict']}", ""])
    return "\n".join(lines)


def write_reports(report_path: Path = REPORT_PATH, json_path: Path = JSON_PATH) -> dict:
    report_path.parent.mkdir(parents=True, exist_ok=True)
    json_path.parent.mkdir(parents=True, exist_ok=True)
    payload = build_payload()
    json_path.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    report_path.write_text(render_markdown(payload), encoding="utf-8")
    return payload


def main() -> None:
    write_reports()
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {JSON_PATH}")


if __name__ == "__main__":
    main()
