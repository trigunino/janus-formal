from __future__ import annotations

from pathlib import Path
import json
import sys


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_phi_scouple_anti_rustine_gate import build_payload as build_anti_rustine_gate


REPORT_PATH = Path("outputs/reports/p0_phi_scouple_source_or_axiom_decision.md")
JSON_PATH = Path("outputs/reports/p0_phi_scouple_source_or_axiom_decision.json")


def build_payload() -> dict:
    anti_rustine = build_anti_rustine_gate()
    source_scan_rows = [
        {
            "source": "M15",
            "found": "coupled field equations with determinant cross-source factors",
            "missing": "no explicit Phi/Phi_bar potential or S_couple selecting phi/L",
        },
        {
            "source": "M30",
            "found": "mixed stationary source form and Bianchi motivation",
            "missing": "no unique variational phi/L selector",
        },
        {
            "source": "local Stueckelberg action test",
            "found": "formal E_phi/E_L once Phi/Phi_bar are declared",
            "missing": "source-derived rule fixing Phi/Phi_bar",
        },
    ]
    minimal_axiom = {
        "name": "A_phi_scouple",
        "statement": (
            "There exists a mirror-symmetric, no-fit S_couple[g_plus,g_minus,phi,L,T_plus,T_minus] "
            "whose variations define K_plus, K_minus, E_phi and E_L, with L shared by K transport and Q_cross."
        ),
        "mandatory_constraints": [
            "mirror Phi_bar = exchange(Phi)",
            "B_4vol determinant source factors match M15 in both sectors",
            "L_plus_to_minus = L_minus_to_plus^{-1}",
            "weak-field dust limit recovers Janus sign matrix",
            "no observational fit constants",
        ],
        "acceptance_tests": [
            "derive K_plus and K_minus by metric variation",
            "derive phi/L selection by E_phi=0 and E_L=0",
            "prove split Noether identities imply R_plus=R_minus=0",
            "recover single cross-dust hE=rho hCuu branch",
            "extend pressure/Pi explicitly or block non-dust claims",
        ],
    }
    decision = {
        "source_derived_phi_or_scouple_found": False,
        "can_close_dynamic_selection_without_new_axiom": False,
        "minimal_axiom_route_available": True,
        "anti_rustine_gate_passed": bool(anti_rustine["variational_acceptance_gate_passed"]),
        "variational_acceptance_gate_passed": bool(anti_rustine["variational_acceptance_gate_passed"]),
        "multiple_no_fit_candidates_remain_possible": bool(
            anti_rustine["multiple_no_fit_candidates_remain_possible"]
        ),
        "axiom_adopted": False,
        "reason": (
            "Available Janus sources anchor determinant-weighted cross sources and geodesic sectors, "
            "but do not supply the unique variational coupling that selects phi/L; "
            "the local S_couple shapes also fail the variational acceptance gate."
        ),
    }
    return {
        "description": "Decision gate for Phi/Phi_bar or S_couple: source-derived closure versus explicit axiom.",
        "status": "source-not-found-minimal-axiom-defined-not-adopted",
        "source_scan_rows": source_scan_rows,
        "minimal_axiom": minimal_axiom,
        "decision": decision,
        "dynamic_phi_l_selection_closed": False,
        "mirror_inverse_consistency_closed": True,
        "single_cross_dust_branch_closed": True,
        "new_axiom_required_for_progress": True,
        "anti_rustine_gate_available": True,
        "anti_rustine_gate_status": anti_rustine["status"],
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "No source-derived Phi/Phi_bar or S_couple is available in the current local Janus corpus. "
            "Further closure requires either a newly found source equation or explicit adoption of A_phi_scouple."
        ),
    }


def render_markdown(payload: dict) -> str:
    axiom = payload["minimal_axiom"]
    decision = payload["decision"]
    lines = [
        "# P0 Phi/S_couple Source Or Axiom Decision",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Dynamic phi/L selection closed: {payload['dynamic_phi_l_selection_closed']}",
        f"Mirror inverse consistency closed: {payload['mirror_inverse_consistency_closed']}",
        f"Single cross-dust branch closed: {payload['single_cross_dust_branch_closed']}",
        f"New axiom required for progress: {payload['new_axiom_required_for_progress']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Source Scan",
        "",
    ]
    for row in payload["source_scan_rows"]:
        lines.append(f"- {row['source']}: found={row['found']}; missing={row['missing']}")
    lines.extend(
        [
            "",
            "## Decision",
            "",
            f"Source-derived Phi/S_couple found: {decision['source_derived_phi_or_scouple_found']}",
            (
                "Can close dynamic selection without new axiom: "
                f"{decision['can_close_dynamic_selection_without_new_axiom']}"
            ),
            f"Minimal axiom route available: {decision['minimal_axiom_route_available']}",
            f"Anti-rustine gate passed: {decision['anti_rustine_gate_passed']}",
            f"Variational acceptance gate passed: {decision['variational_acceptance_gate_passed']}",
            (
                "Multiple no-fit candidates remain possible: "
                f"{decision['multiple_no_fit_candidates_remain_possible']}"
            ),
            f"Axiom adopted: {decision['axiom_adopted']}",
            f"Reason: {decision['reason']}",
            "",
            "## Minimal Axiom Candidate",
            "",
            f"Name: `{axiom['name']}`",
            f"Statement: {axiom['statement']}",
            "",
            "Mandatory constraints:",
        ]
    )
    lines.extend(f"- {item}" for item in axiom["mandatory_constraints"])
    lines.extend(["", "Acceptance tests:"])
    lines.extend(f"- {item}" for item in axiom["acceptance_tests"])
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
