from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_stueckelberg_popt_reduced_sachs_candidate.md")
JSON_PATH = Path("outputs/reports/p0_stueckelberg_popt_reduced_sachs_candidate.json")


def build_payload() -> dict:
    candidate = {
        "name": "reduced_sachs_null_source",
        "formula": "Q_cross_sachs = k_mu k_nu T_to^{mu nu}",
        "dropped_until_derived": "m_mu mbar_nu T_to^{mu nu} screen term",
        "free_parameters": [],
    }
    tests = [
        {
            "name": "sachs_source_match",
            "passes": True,
            "reason": "Raychaudhuri focusing source uses Ricci/null-null contraction",
        },
        {
            "name": "same_transport",
            "passes": True,
            "reason": "uses the same transported T_to or kinetic moment",
        },
        {
            "name": "janus_sign",
            "passes": False,
            "reason": "field-equation sign for positive/negative sector still not substituted",
        },
        {
            "name": "full_lensing_observable",
            "passes": False,
            "reason": "shear, Weyl/tidal terms, distances, and gauge conventions remain outside this scalar source",
        },
    ]
    decision = {
        "reduced_candidate_accepted_for_diagnostic": True,
        "screen_term_rejected_until_derived": True,
        "prediction_ready": False,
        "reason": (
            "The reduced Sachs candidate is stricter than the previous P_opt: keep only "
            "the null-null stress source that the optical equation directly asks for. "
            "This is diagnostic until Janus sign and full lensing observable chain close."
        ),
    }
    return {
        "artifact": "p0_stueckelberg_popt_reduced_sachs_candidate",
        "status": "reduced-sachs-candidate-diagnostic-only",
        "fit_used": False,
        "physics_closed": False,
        "prediction_ready": False,
        "candidate": candidate,
        "tests": tests,
        "decision": decision,
    }


def render_markdown(payload: dict) -> str:
    candidate = payload["candidate"]
    decision = payload["decision"]
    lines = [
        "# P0 Stueckelberg P_opt Reduced Sachs Candidate",
        "",
        f"Status: {payload['status']}",
        f"Fit used: {payload['fit_used']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Candidate",
        f"Name: {candidate['name']}",
        f"Formula: `{candidate['formula']}`",
        f"Dropped until derived: {candidate['dropped_until_derived']}",
        f"Free parameters: {candidate['free_parameters']}",
        "",
        "## Tests",
    ]
    for row in payload["tests"]:
        lines.append(f"- {row['name']}: passes={row['passes']}; {row['reason']}")
    lines.extend(
        [
            "",
            "## Decision",
            f"Reduced candidate accepted for diagnostic: {decision['reduced_candidate_accepted_for_diagnostic']}",
            f"Screen term rejected until derived: {decision['screen_term_rejected_until_derived']}",
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
