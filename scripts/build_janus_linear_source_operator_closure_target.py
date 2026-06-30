from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/janus_linear_source_operator_closure_target.md")
JSON_PATH = Path("outputs/reports/janus_linear_source_operator_closure_target.json")


def build_payload() -> dict:
    closure_rows = [
        {
            "object": "Omega_plus(a)",
            "source_rule": "derive from the chosen Janus positive-sector background",
            "blocks": "linear M(a), growth D_plus, theta_plus",
            "closed": False,
        },
        {
            "object": "Omega_minus_eff(a)",
            "source_rule": "derive in the same positive-effective density measure as Q_det",
            "blocks": "linear M(a), growth D_minus, theta_minus",
            "closed": False,
        },
        {
            "object": "A_J",
            "source_rule": "derive from source normalization or declare no-fit comparison",
            "blocks": "physical transfer amplitude",
            "closed": False,
        },
        {
            "object": "theta_s(k,a)",
            "source_rule": "derive from continuity and verify with Euler/geodesic sign",
            "blocks": "source-derived beta_vec",
            "closed": False,
        },
    ]
    consistency_checks = [
        "one branch supplies density, growth, velocity and amplitude",
        "negative-proper density cannot enter before Q_det convention is fixed",
        "theta_s and v_s must use the same H(a)=H0 E_J(a)",
        "no sigma8/S8/survey normalization substitutes for A_J",
        "constant Omega propagation remains diagnostic",
    ]
    return {
        "description": "Closure target for the Janus linear source operator feeding physical ICs and beta.",
        "status": "source-operator-closure-open",
        "closure_rows": closure_rows,
        "consistency_checks": consistency_checks,
        "source_operator_closed": False,
        "source_derived_ic_ready": False,
        "source_derived_beta_ready": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "The linear source operator is localized but not closed. Omega_s(a), A_J "
            "and theta_s must be derived together before beta or ICs become physical."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# Janus Linear Source Operator Closure Target",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Source operator closed: {payload['source_operator_closed']}",
        f"Source-derived IC ready: {payload['source_derived_ic_ready']}",
        f"Source-derived beta ready: {payload['source_derived_beta_ready']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Closure Rows",
        "",
        "| object | source rule | blocks | closed |",
        "|---|---|---|---|",
    ]
    for row in payload["closure_rows"]:
        lines.append(
            f"| `{row['object']}` | {row['source_rule']} | {row['blocks']} | {row['closed']} |"
        )
    lines.extend(["", "## Consistency Checks", ""])
    lines.extend(f"- {item}" for item in payload["consistency_checks"])
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
