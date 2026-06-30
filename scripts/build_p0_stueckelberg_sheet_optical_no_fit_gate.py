from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_stueckelberg_sheet_optical_no_fit_gate.md")
JSON_PATH = Path("outputs/reports/p0_stueckelberg_sheet_optical_no_fit_gate.json")


def build_payload() -> dict:
    optical_rules = [
        {
            "name": "same_distribution",
            "rule": "Q_cross_total is computed from the same sheets or f_to used for stress transport",
            "status": "required",
        },
        {
            "name": "linear_sheet_sum",
            "rule": "Q_cross_total = sum_s Q_cross[phi_s,L_s,w_s]",
            "status": "diagnostic-form",
        },
        {
            "name": "no_sheet_amplitude",
            "rule": "no alpha_s Q_cross_s factors are allowed",
            "status": "enforced",
        },
        {
            "name": "qdet_separate",
            "rule": "density/volume determinant weights are not lensing amplitudes",
            "status": "enforced",
        },
    ]
    failure_modes = [
        "choosing sheet optical weights independently from transported mass",
        "absorbing missing pressure/Pi into Q_cross_total",
        "using a different L for optical transport than for stress transport",
        "normalizing Q_cross_total to match observations before closure",
    ]
    decision = {
        "optical_no_fit_gate_defined": True,
        "independent_lensing_amplitudes_allowed": False,
        "source_derived_optics_closed": False,
        "physics_closed": False,
        "prediction_ready": False,
        "reason": (
            "The sheet optical contribution must be a projection/moment of the same "
            "transport data used for stress. Any independent sheet amplitude would be "
            "a fit and is rejected."
        ),
    }
    return {
        "artifact": "p0_stueckelberg_sheet_optical_no_fit_gate",
        "status": "sheet-optical-no-fit-gate-open",
        "fit_used": False,
        "free_parameters": [],
        "physics_closed": False,
        "prediction_ready": False,
        "optical_rules": optical_rules,
        "failure_modes": failure_modes,
        "decision": decision,
    }


def render_markdown(payload: dict) -> str:
    decision = payload["decision"]
    lines = [
        "# P0 Stueckelberg Sheet Optical No-Fit Gate",
        "",
        f"Status: {payload['status']}",
        f"Fit used: {payload['fit_used']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Optical Rules",
    ]
    for row in payload["optical_rules"]:
        lines.append(f"- {row['name']}: {row['rule']} (status={row['status']})")
    lines.extend(["", "## Failure Modes"])
    lines.extend(f"- {item}" for item in payload["failure_modes"])
    lines.extend(
        [
            "",
            "## Decision",
            f"Optical no-fit gate defined: {decision['optical_no_fit_gate_defined']}",
            f"Independent lensing amplitudes allowed: {decision['independent_lensing_amplitudes_allowed']}",
            f"Source-derived optics closed: {decision['source_derived_optics_closed']}",
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
