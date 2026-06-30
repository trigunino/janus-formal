from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_flat_vs_holonomy_decision.md")
JSON_PATH = Path("outputs/reports/p0_flat_vs_holonomy_decision.json")


def build_payload() -> dict:
    branches = [
        {
            "branch": "pure_gauge_flat",
            "use_when": "Lorentz L is global/smooth and relative holonomy is unphysical gauge",
            "must_prove": ["regular Lorentz projection", "R_Omega=0", "zero-divergence PDE closure"],
            "accepted": False,
        },
        {
            "branch": "relative_holonomy_nonflat",
            "use_when": "sector curvature mismatch makes path dependence physical",
            "must_prove": ["source path rule", "same path for K/Qcross", "zero-divergence PDE closure"],
            "accepted": False,
        },
    ]
    decision_rule = [
        "start with pure_gauge_flat as simplest diagnostic branch",
        "reject flat branch if it fails zero-divergence PDE or erases required curvature effects",
        "promote holonomy branch only with source-derived path rule",
        "neither branch is prediction-ready without K/Qcross consistency",
    ]
    return {
        "description": "P0 decision matrix for flat pure-gauge versus non-flat relative-holonomy L transport.",
        "status": "flat-vs-holonomy-open",
        "decision_written": True,
        "accepted_branch": None,
        "physics_closed": False,
        "prediction_ready": False,
        "branches": branches,
        "decision_rule": decision_rule,
        "verdict": (
            "The next computational test should use the flat pure-gauge branch first, "
            "then fall back to relative holonomy only if flat transport fails source "
            "or PDE consistency."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Flat Vs Holonomy Decision",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Accepted branch: {payload['accepted_branch']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "| branch | use when | must prove | accepted |",
        "|---|---|---|---|",
    ]
    for row in payload["branches"]:
        lines.append(
            f"| {row['branch']} | {row['use_when']} | {'; '.join(row['must_prove'])} | {row['accepted']} |"
        )
    lines.extend(["", "## Decision Rule", ""])
    lines.extend(f"- {item}" for item in payload["decision_rule"])
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
