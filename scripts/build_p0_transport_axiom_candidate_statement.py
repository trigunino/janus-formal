from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_transport_axiom_candidate_statement.md")
JSON_PATH = Path("outputs/reports/p0_transport_axiom_candidate_statement.json")


def build_payload() -> dict:
    axiom_statement = {
        "scope": "rank-one dust only",
        "one_l_omega": (
            "Use one cross-sector Lorentz map L and its connection "
            "Omega_alpha=(D_alpha L)L^{-1}."
        ),
        "dust_annihilation": (
            "For each transported rank-one dust congruence, "
            "Omega_u u=0 with Omega_u=u^alpha Omega_alpha."
        ),
        "mirror_inverse": (
            "The mirror map is the inverse: L_plus_to_minus=L_minus_to_plus^{-1}; "
            "its Omega law is the corresponding inverse transport law."
        ),
        "same_observable_chain": (
            "The same L/Omega is used in residual closure, K transport, Q_cross, "
            "and lensing contractions; no independent optical transport is allowed."
        ),
        "exclusions": (
            "Pressure, projector, Pi, and non-rank-one extensions are excluded until "
            "separately derived."
        ),
        "no_fit_rule": "No parameter fit, lensing fit, or post-hoc component choice is part of this candidate.",
    }
    checks = [
        {
            "id": "same_l_omega",
            "statement": axiom_statement["one_l_omega"],
            "satisfied_by_candidate": True,
        },
        {
            "id": "omega_u_zero_rank_one_dust",
            "statement": axiom_statement["dust_annihilation"],
            "satisfied_by_candidate": True,
        },
        {
            "id": "mirror_inverse",
            "statement": axiom_statement["mirror_inverse"],
            "satisfied_by_candidate": True,
        },
        {
            "id": "same_k_qcross_lensing",
            "statement": axiom_statement["same_observable_chain"],
            "satisfied_by_candidate": True,
        },
        {
            "id": "pressure_pi_excluded",
            "statement": axiom_statement["exclusions"],
            "satisfied_by_candidate": True,
        },
        {
            "id": "no_fit",
            "statement": axiom_statement["no_fit_rule"],
            "satisfied_by_candidate": True,
        },
    ]
    return {
        "description": "Bounded P0 artifact writing a complete candidate transport axiom without adopting it.",
        "status": "candidate-statement-only",
        "candidate_written": True,
        "adopted": False,
        "prediction": False,
        "prediction_ready": False,
        "rank_one_dust_scope": True,
        "pressure_pi_excluded": True,
        "fit_used": False,
        "axiom_statement": axiom_statement,
        "candidate_checks": checks,
        "verdict": (
            "The candidate axiom is now explicit and complete for rank-one dust, but "
            "this artifact does not adopt it, derive it from Janus sources, extend it "
            "to pressure/Pi, or authorize any prediction."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Transport Axiom Candidate Statement",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Candidate written: {payload['candidate_written']}",
        f"Adopted: {payload['adopted']}",
        f"Prediction: {payload['prediction']}",
        f"Prediction ready: {payload['prediction_ready']}",
        f"Rank-one dust scope: {payload['rank_one_dust_scope']}",
        f"Pressure/Pi excluded: {payload['pressure_pi_excluded']}",
        f"Fit used: {payload['fit_used']}",
        "",
        "## Candidate Axiom",
        "",
    ]
    for key, value in payload["axiom_statement"].items():
        lines.append(f"- {key}: {value}")
    lines.extend(["", "## Candidate Checks", ""])
    lines.extend(["| id | satisfied | statement |", "|---|---|---|"])
    for row in payload["candidate_checks"]:
        lines.append(f"| {row['id']} | {row['satisfied_by_candidate']} | {row['statement']} |")
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
