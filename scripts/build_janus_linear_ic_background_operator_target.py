from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/janus_linear_ic_background_operator_target.md")
JSON_PATH = Path("outputs/reports/janus_linear_ic_background_operator_target.json")


def build_payload() -> dict:
    required_functions = [
        {
            "name": "Omega_plus(a)",
            "status": "missing_source_derivation",
            "rule": "positive-sector background fraction for the chosen Janus branch",
        },
        {
            "name": "Omega_minus_eff(a)",
            "status": "missing_source_derivation",
            "rule": "negative sector in positive-effective density measure; negative_proper requires Q_det first",
        },
        {
            "name": "Omega_abs(a)",
            "status": "missing_source_derivation",
            "rule": "Omega_plus(a)+Omega_minus_eff(a), not an inferred fit parameter",
        },
    ]
    operator = {
        "matrix": "M(a) = (3/2) [[Omega_plus(a), -Omega_minus_eff(a)], [-Omega_plus(a), Omega_minus_eff(a)]]",
        "friction": "A(a) = 2 + d ln(H) / d ln(a), H(a)=H0 E_J(a)",
        "branch": "positive_effective density branch until Q_det negative_proper map is derived",
    }
    blocked_outputs = [
        "A_J remains blocked_no_fit",
        "T_J(k,a_ic) remains missing",
        "do not replace T_J with Lambda-CDM transfer, Gaussian cutoff, lognormal, bounded tanh, or survey-fitted shape",
        "propagator constants omega_plus/omega_minus remain diagnostics until these functions are sourced",
    ]
    return {
        "description": "Source-provenance gate for Janus linear IC background operator.",
        "source_anchors": [
            "M18 expansion E_J(a)",
            "M15/M30 weak-field signed source",
            "Q_det density-measure target",
        ],
        "physics_closed": False,
        "required_functions": required_functions,
        "operator": operator,
        "blocked_outputs": blocked_outputs,
        "verdict": (
            "Before production ICs, Omega_plus(a) and Omega_minus_eff(a) must be "
            "source-derived. Current constant-Omega propagation remains diagnostic only."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# Janus Linear IC Background Operator Target",
        "",
        payload["description"],
        "",
        f"Physics closed: {payload['physics_closed']}",
        "",
        "## Required Functions",
        "",
        "| function | status | rule |",
        "|---|---|---|",
    ]
    for row in payload["required_functions"]:
        lines.append(f"| `{row['name']}` | {row['status']} | {row['rule']} |")
    lines.extend(["", "## Operator", ""])
    for key, value in payload["operator"].items():
        lines.append(f"- `{key}`: `{value}`")
    lines.extend(["", "## Blocked Outputs", ""])
    lines.extend(f"- {item}" for item in payload["blocked_outputs"])
    lines.extend(["", f"Verdict: {payload['verdict']}", ""])
    return "\n".join(lines)


def main() -> None:
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    payload = build_payload()
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(render_markdown(payload), encoding="utf-8")
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {JSON_PATH}")


if __name__ == "__main__":
    main()
