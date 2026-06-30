from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_source_measure_selection_rules.md")
JSON_PATH = Path("outputs/reports/p0_source_measure_selection_rules.json")


def build_payload() -> dict:
    selection_rules = [
        {
            "rule": "field-equation measure",
            "accept_if": "Janus source term is written as sqrt(-g_other)/sqrt(-g_self) times transported T_other",
            "required_terms": ["D log B_4vol", "lapse derivative", "connection-difference terms"],
            "reject_if_missing": ["D log B_4vol"],
        },
        {
            "rule": "dust slice measure",
            "accept_if": "Janus source derivation explicitly projects to a spatial dust flux before reinsertion",
            "required_terms": ["D log V3_dust", "slicing/lapse reinsertion proof", "same L map as K/Q_cross"],
            "reject_if_missing": ["slicing/lapse reinsertion proof"],
        },
        {
            "rule": "effective density measure",
            "accept_if": "rho_eff definition declares exactly which measure is already absorbed",
            "required_terms": ["absorbed-measure declaration", "no later Q_det multiplication"],
            "reject_if_missing": ["absorbed-measure declaration"],
        },
    ]
    residual_tests = [
        "substitute selected source measure into R_plus",
        "substitute mirror selected source measure into R_minus",
        "expand product-rule derivatives before cancellation claims",
        "verify pressure and Pi terms remain tensor terms, not scalar density factors",
        "verify Q_cross is only the optical/tetrad projection factor",
    ]
    return {
        "description": "P0 rules for selecting one source-measure convention without scalar patching.",
        "status": "selection-rules-written-convention-open",
        "selection_rules_written": True,
        "single_convention_required": True,
        "accepted_rule": None,
        "r_plus_closed": False,
        "r_minus_closed": False,
        "physics_closed": False,
        "prediction_ready": False,
        "selection_rules": selection_rules,
        "residual_tests": residual_tests,
        "forbidden": [
            "mix B_4vol and V3_dust in one branch",
            "multiply rho_eff by Q_det after absorption",
            "use Q_cross as a source-density convention",
            "drop lapse terms by notation change",
        ],
        "verdict": (
            "The next admissible step is substitution into R_plus/R_minus. "
            "No rule is accepted until both residuals close with source traceability."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Source-Measure Selection Rules",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Accepted rule: {payload['accepted_rule']}",
        f"R_plus closed: {payload['r_plus_closed']}",
        f"R_minus closed: {payload['r_minus_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Selection Rules",
        "",
    ]
    for row in payload["selection_rules"]:
        lines.append(f"- {row['rule']}:")
        lines.append(f"  - accept if: {row['accept_if']}")
        lines.append(f"  - required terms: {', '.join(row['required_terms'])}")
        lines.append(f"  - reject if missing: {', '.join(row['reject_if_missing'])}")
    lines.extend(["", "## Residual Tests", ""])
    lines.extend(f"- {item}" for item in payload["residual_tests"])
    lines.extend(["", "## Forbidden", ""])
    lines.extend(f"- {item}" for item in payload["forbidden"])
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
