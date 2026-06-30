from __future__ import annotations

from pathlib import Path
import json
import sys


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_pulled_particle_action_cuu_derivation import (
    build_payload as build_particle_derivation,
)


REPORT_PATH = Path("outputs/reports/p0_pulled_dust_el_cuu_substitution_proof.md")
JSON_PATH = Path("outputs/reports/p0_pulled_dust_el_cuu_substitution_proof.json")


def build_payload() -> dict:
    particle = build_particle_derivation()
    proof_rows = [
        {
            "row": "projected_dust_variation",
            "substitution": "h div(T_dust) = rho h a_to",
            "status": "standard-closed",
        },
        {
            "row": "dphi_density_measure",
            "substitution": "delta(B rho) -> D_receiver(B_4vol rho_to u_to)",
            "status": "closed-for-single-cross-dust",
        },
        {
            "row": "dl_velocity_tetrad",
            "substitution": "D L terms -> flow-projected F_alpha rows",
            "status": "same-map-bridge-closed-dynamic-selection-open",
        },
        {
            "row": "connection_force",
            "substitution": "h a_to -> h C_self-other(u_to,u_to)",
            "status": "closed-for-single-cross-dust",
        },
        {
            "row": "mirror_inverse",
            "substitution": "minus row follows from inverse phi/L",
            "status": "closed-if-inverse-constraint-in-action",
        },
        {
            "row": "dynamic_phi_l_selection",
            "substitution": "Janus source/action uniquely selects phi/L",
            "status": "open-source-action-gap",
            "next_gate": "p0_phi_scouple_source_or_axiom_decision",
        },
    ]
    conclusion = {
        "formula": "h E_phi/E_L = rho h C(u_to,u_to)",
        "proved": False,
        "conditional_progress": True,
        "reason": (
            "The standard dust projection row is closed, but measure, D_L, connection-force "
            "rows are now closed for a declared single cross-dust pullback; dynamic phi/L "
            "selection remains open."
        ),
    }
    closure_needed = [
        "derive dynamic phi/L selection from Janus action/source equations",
        "check sign convention after both mirror rows are written",
        "keep pressure/Pi outside this dust-only proof",
    ]
    return {
        "description": "Proof-style substitution ledger for deriving hE=rho hCuu from pulled dust.",
        "status": "substitution-proof-open",
        "proof_rows": proof_rows,
        "conclusion": conclusion,
        "closure_needed": closure_needed,
        "particle_action_cuu_derivation_status": particle["status"],
        "particle_geodesic_variation_closed": particle["particle_geodesic_variation_closed"],
        "cold_dust_lift_closed": particle["cold_dust_lift_closed"],
        "cross_pullback_closed": particle["connection_difference_cross_pullback_closed"],
        "standard_projection_closed": True,
        "single_cross_dust_rows_closed": True,
        "mirror_inverse_closed": True,
        "dynamic_phi_l_selection_closed": False,
        "phi_scouple_source_or_axiom_decision_available": True,
        "all_rows_closed": False,
        "projected_cuu_identity_proved": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "This is the assembled proof state. It reaches the target formula only "
            "conditionally; the remaining open rows are explicit."
        ),
    }


def render_markdown(payload: dict) -> str:
    conclusion = payload["conclusion"]
    lines = [
        "# P0 Pulled Dust EL Cuu Substitution Proof",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Particle action Cuu derivation status: {payload['particle_action_cuu_derivation_status']}",
        f"Particle geodesic variation closed: {payload['particle_geodesic_variation_closed']}",
        f"Cold dust lift closed: {payload['cold_dust_lift_closed']}",
        f"Cross pullback closed: {payload['cross_pullback_closed']}",
        f"Standard projection closed: {payload['standard_projection_closed']}",
        f"All rows closed: {payload['all_rows_closed']}",
        f"Projected Cuu identity proved: {payload['projected_cuu_identity_proved']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Proof Rows",
        "",
    ]
    for row in payload["proof_rows"]:
        lines.append(f"- {row['row']}: `{row['substitution']}` ({row['status']})")
    lines.extend(
        [
            "",
            "## Conclusion",
            "",
            f"- formula: `{conclusion['formula']}`",
            f"- proved: {conclusion['proved']}",
            f"- conditional progress: {conclusion['conditional_progress']}",
            f"- reason: {conclusion['reason']}",
            "",
            "## Closure Needed",
            "",
        ]
    )
    lines.extend(f"- {item}" for item in payload["closure_needed"])
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
