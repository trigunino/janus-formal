from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_stueckelberg_zero_param_progression.md")
JSON_PATH = Path("outputs/reports/p0_stueckelberg_zero_param_progression.json")


def build_payload() -> dict:
    steps = [
        {
            "step": "fix_phi_family",
            "result": "zero_parameter_normalized_copy branch exposed",
            "closed": True,
        },
        {
            "step": "write_explicit_action",
            "result": "K_plus/K_minus and formal E_phi/E_L can be defined",
            "closed": True,
        },
        {
            "step": "test_e_phi_e_l_compatibility",
            "result": "requires transported dust continuity and map compatibility",
            "closed": False,
        },
        {
            "step": "substitute_residuals",
            "result": "must verify R_plus=0 and R_minus=0 after Dphi/DL/DlogB terms",
            "closed": False,
        },
        {
            "step": "prediction_gate",
            "result": "locked until compatibility and residual substitution close",
            "closed": False,
        },
    ]
    return {
        "description": "Progression tracker for the zero-parameter Stueckelberg dust branch.",
        "status": "progression-partial",
        "zero_parameter_branch": "available",
        "structural_action_test": "passed",
        "compatibility_closed": False,
        "residuals_closed": False,
        "physics_closed": False,
        "prediction_ready": False,
        "steps": steps,
        "non_fit_constraints": [
            "no observational amplitude",
            "same phi/L for K and Q_cross",
            "M15/M30 sign recovery",
            "mirror density convention",
        ],
        "verdict": (
            "The branch has real progress: amplitude fitting is removed and the action "
            "structure exists. The remaining blockers are now specific equations, not "
            "vague scaffolds: E_phi/E_L compatibility and residual substitution."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Stueckelberg Zero-Parameter Progression",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Zero-parameter branch: {payload['zero_parameter_branch']}",
        f"Structural action test: {payload['structural_action_test']}",
        f"Compatibility closed: {payload['compatibility_closed']}",
        f"Residuals closed: {payload['residuals_closed']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "| step | result | closed |",
        "|---|---|---|",
    ]
    for row in payload["steps"]:
        lines.append(f"| {row['step']} | {row['result']} | {row['closed']} |")
    lines.extend(["", "## Non-Fit Constraints", ""])
    lines.extend(f"- {item}" for item in payload["non_fit_constraints"])
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
