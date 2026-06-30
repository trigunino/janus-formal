from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_gauge_lifting_decision_matrix.md")
JSON_PATH = Path("outputs/reports/p0_gauge_lifting_decision_matrix.json")


def build_payload() -> dict:
    branches = [
        {
            "branch": "Pi eigenframe",
            "can_fix": "continuous rest-space orientation if Pi is nonzero and nondegenerate",
            "needs": ["source-derived Pi evolution", "nondegenerate physical Pi", "R_plus/R_minus with Pi"],
            "risk": "not applicable for dust or degenerate Pi",
            "priority": 2,
            "accepted": False,
        },
        {
            "branch": "boundary/initial L",
            "can_fix": "integration constants and global orientation of L",
            "needs": ["source/symmetry boundary", "Omega integrability", "path rule"],
            "risk": "can become hidden lensing fit if boundary is observational",
            "priority": 1,
            "accepted": False,
        },
        {
            "branch": "action/gauge principle",
            "can_fix": "select Omega among zero-divergence PDE solutions",
            "needs": ["variational or symmetry principle", "no-fit criterion", "same K/Qcross L"],
            "risk": "new axiom unless derived from Janus action/symmetry",
            "priority": 3,
            "accepted": False,
        },
    ]
    immediate_next = [
        "search sources for boundary/initial L anchors",
        "search sources for Pi evolution anchors",
        "search sources for action/gauge selection anchors",
        "if no source closes them, build explicit axiom branches and keep prediction_ready=false",
    ]
    return {
        "description": "Decision matrix for lifting the transverse Omega/F_alpha gauge freedom.",
        "status": "decision-matrix-open",
        "branches_ranked": True,
        "accepted_branch": None,
        "physics_closed": False,
        "prediction_ready": False,
        "branches": branches,
        "immediate_next": immediate_next,
        "verdict": (
            "Boundary/initial L is the first branch to test because it can fix "
            "integration constants without requiring non-dust matter. Pi is stronger "
            "when present. Action/gauge selection is broadest but riskiest as a new axiom."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Gauge-Lifting Decision Matrix",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Accepted branch: {payload['accepted_branch']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "| branch | can fix | needs | risk | priority | accepted |",
        "|---|---|---|---|---:|---|",
    ]
    for row in payload["branches"]:
        lines.append(
            f"| {row['branch']} | {row['can_fix']} | {'; '.join(row['needs'])} | {row['risk']} | {row['priority']} | {row['accepted']} |"
        )
    lines.extend(["", "## Immediate Next", ""])
    lines.extend(f"- {item}" for item in payload["immediate_next"])
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
