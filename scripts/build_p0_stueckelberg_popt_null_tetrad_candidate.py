from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_stueckelberg_popt_null_tetrad_candidate.md")
JSON_PATH = Path("outputs/reports/p0_stueckelberg_popt_null_tetrad_candidate.json")


def build_payload() -> dict:
    candidate = {
        "name": "null_tetrad_stress_projection",
        "formula": "Q_cross[k,m] = (k_mu k_nu + m_mu mbar_nu + mbar_mu m_nu) T_to^{mu nu}",
        "inputs": ["receiver null/tetrad frame", "same L", "same transported T_to", "g_plus/g_minus through frame construction"],
        "free_parameters": [],
    }
    tests = [
        {
            "name": "geometric_only",
            "passes": True,
            "reason": "uses only metric/tetrad/null frame and transported stress",
        },
        {
            "name": "same_transport",
            "passes": True,
            "reason": "T_to is the kinetic/sheet stress already used by matter transport",
        },
        {
            "name": "no_scalar_fit",
            "passes": True,
            "reason": "no amplitude multiplier is introduced",
        },
        {
            "name": "single_sheet_limit",
            "passes": "conditional",
            "reason": "reduces to projected rho u u, but must match Janus published optical sign/convention",
        },
        {
            "name": "physical_lensing_law",
            "passes": False,
            "reason": "does not yet derive the Sachs/optical equation coupling or Janus negative-mass sign",
        },
    ]
    decision = {
        "popt_candidate_constructed": True,
        "acceptance_tests_pass": "partial",
        "source_derived_lensing_closed": False,
        "prediction_ready": False,
        "reason": (
            "The null-tetrad stress projection is the minimal no-fit P_opt candidate. "
            "It passes geometric/same-transport/no-fit tests, but it is not yet a "
            "derived Janus lensing law because the optical equation and sign convention "
            "still have to be proven from source geometry."
        ),
    }
    return {
        "artifact": "p0_stueckelberg_popt_null_tetrad_candidate",
        "status": "popt-candidate-partial-pass-open",
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
        "# P0 Stueckelberg P_opt Null-Tetrad Candidate",
        "",
        f"Status: {payload['status']}",
        f"Fit used: {payload['fit_used']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Candidate",
        f"Name: {candidate['name']}",
        f"Formula: `{candidate['formula']}`",
        f"Inputs: {candidate['inputs']}",
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
            f"P_opt candidate constructed: {decision['popt_candidate_constructed']}",
            f"Acceptance tests pass: {decision['acceptance_tests_pass']}",
            f"Source-derived lensing closed: {decision['source_derived_lensing_closed']}",
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
