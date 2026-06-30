from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_stueckelberg_sheet_diagnostic_execution_gate.md")
JSON_PATH = Path("outputs/reports/p0_stueckelberg_sheet_diagnostic_execution_gate.json")


def build_payload() -> dict:
    allowed = [
        "pre-caustic worldline ODE transport diagnostics",
        "post-caustic cold-sheet stress summation diagnostics",
        "mass-weight and momentum-balance consistency checks",
        "Q_cross bookkeeping from the same sheet/f_to data without normalization fit",
    ]
    blocked = [
        "claiming physical lensing prediction",
        "sigma8 normalization on current grid",
        "pressure/Pi closure",
        "post-caustic kinetic transport as Janus-derived closure",
    ]
    required_outputs = [
        "caustic flag per cell/sheet",
        "sheet mass-weight conservation residual",
        "mirror support mismatch residual",
        "same-L/Q_cross consistency residual",
        "separate Q_det and Q_cross columns",
    ]
    decision = {
        "diagnostic_execution_allowed": True,
        "prediction_execution_allowed": False,
        "simulation_scope": "diagnostic-only-sheet-aware",
        "physics_closed": False,
        "prediction_ready": False,
        "reason": (
            "The math supports a diagnostic simulator that tracks exactly where the "
            "conditional dust/sheet assumptions hold or fail. It must report residuals "
            "instead of hiding them in fitted amplitudes."
        ),
    }
    return {
        "artifact": "p0_stueckelberg_sheet_diagnostic_execution_gate",
        "status": "diagnostic-execution-allowed-prediction-blocked",
        "fit_used": False,
        "free_parameters": [],
        "physics_closed": False,
        "prediction_ready": False,
        "allowed": allowed,
        "blocked": blocked,
        "required_outputs": required_outputs,
        "decision": decision,
    }


def render_markdown(payload: dict) -> str:
    decision = payload["decision"]
    lines = [
        "# P0 Stueckelberg Sheet Diagnostic Execution Gate",
        "",
        f"Status: {payload['status']}",
        f"Fit used: {payload['fit_used']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Allowed",
    ]
    lines.extend(f"- {item}" for item in payload["allowed"])
    lines.extend(["", "## Blocked"])
    lines.extend(f"- {item}" for item in payload["blocked"])
    lines.extend(["", "## Required Outputs"])
    lines.extend(f"- {item}" for item in payload["required_outputs"])
    lines.extend(
        [
            "",
            "## Decision",
            f"Diagnostic execution allowed: {decision['diagnostic_execution_allowed']}",
            f"Prediction execution allowed: {decision['prediction_execution_allowed']}",
            f"Simulation scope: {decision['simulation_scope']}",
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
