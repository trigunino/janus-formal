from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_stueckelberg_rkin_commutator_closure_gate.md")
JSON_PATH = Path("outputs/reports/p0_stueckelberg_rkin_commutator_closure_gate.json")


def build_payload() -> dict:
    closure_cases = [
        {
            "case": "full_phase_space_symplectomorphism",
            "condition": "Phi/L maps source Hamiltonian geodesic flow to receiver Hamiltonian geodesic flow",
            "rkin": "0",
            "admissible": "too-strong-unless-Janus-derived",
        },
        {
            "case": "dust_cold_shell",
            "condition": "commutator vanishes only on support of cold sheet distribution",
            "rkin": "zero-on-support",
            "admissible": "diagnostic-conditional",
        },
        {
            "case": "generic_kinetic",
            "condition": "velocity dispersion samples off-shell transverse directions",
            "rkin": "nonzero",
            "admissible": "open",
        },
    ]
    required_proofs = [
        "show Phi/L is canonical or measure-preserving on the mass shell",
        "show mirror inverse acts on phase-space support, not only spacetime labels",
        "show cold-shell support recovers sheet-sum residuals",
        "show nonzero R_kin moments are not hidden in Q_cross or Q_det",
    ]
    decision = {
        "rkin_zero_generically": False,
        "rkin_zero_on_cold_support_possible": True,
        "full_phase_space_closure": False,
        "prediction_ready": False,
        "reason": (
            "The commutator gate shows why full kinetic closure is harder than dust: "
            "Phi/L must intertwine phase-space geodesic flows. Cold support can pass "
            "conditionally, but generic velocity dispersion remains open."
        ),
    }
    return {
        "artifact": "p0_stueckelberg_rkin_commutator_closure_gate",
        "status": "rkin-closure-gate-open",
        "fit_used": False,
        "free_parameters": [],
        "physics_closed": False,
        "prediction_ready": False,
        "closure_cases": closure_cases,
        "required_proofs": required_proofs,
        "decision": decision,
    }


def render_markdown(payload: dict) -> str:
    decision = payload["decision"]
    lines = [
        "# P0 Stueckelberg R_kin Commutator Closure Gate",
        "",
        f"Status: {payload['status']}",
        f"Fit used: {payload['fit_used']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Closure Cases",
    ]
    for row in payload["closure_cases"]:
        lines.append(f"- {row['case']}: {row['condition']}")
        lines.append(f"  - R_kin: {row['rkin']}")
        lines.append(f"  - admissible: {row['admissible']}")
    lines.extend(["", "## Required Proofs"])
    lines.extend(f"- {item}" for item in payload["required_proofs"])
    lines.extend(
        [
            "",
            "## Decision",
            f"R_kin zero generically: {decision['rkin_zero_generically']}",
            f"R_kin zero on cold support possible: {decision['rkin_zero_on_cold_support_possible']}",
            f"Full phase-space closure: {decision['full_phase_space_closure']}",
            f"Prediction ready: {decision['prediction_ready']}",
            f"Reason: {decision['reason']}",
            "",
        ]
    )
    return "\n".join(lines)


def write_reports(report_path: Path = REPORT_PATH, json_path: Path = JSON_PATH) -> dict:
    payload = build_payload()
    report_path.parent.mkdir(parents=True, exist_ok=True)
    report_path.write_text(render_markdown(payload), encoding="utf-8")
    json_path.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    return payload


if __name__ == "__main__":
    write_reports()
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {JSON_PATH}")
