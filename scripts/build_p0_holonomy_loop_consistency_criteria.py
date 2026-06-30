from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_holonomy_loop_consistency_criteria.md")
JSON_PATH = Path("outputs/reports/p0_holonomy_loop_consistency_criteria.json")


CRITERIA = [
    {
        "criterion": "non-flat relative connection",
        "accept": "for R_Omega != 0, transported L is path/family dependent and path choice must be source-derived.",
        "satisfied": False,
    },
    {
        "criterion": "loop constraints",
        "accept": "closed source-receiver loops state explicit holonomy constraints instead of introducing free branch jumps.",
        "satisfied": False,
    },
    {
        "criterion": "segmentation invariance",
        "accept": "subdividing the same declared path/family does not change K or Q_cross transport outputs.",
        "satisfied": False,
    },
    {
        "criterion": "shared K and Q_cross path rule",
        "accept": "the same source-derived path/family is used for Bianchi K and optical Q_cross.",
        "satisfied": False,
    },
    {
        "criterion": "no lensing-fit amplitude",
        "accept": "holonomy amplitude, loop area, and path family are fixed before lensing comparison and cannot be fit to residuals.",
        "satisfied": False,
    },
    {
        "criterion": "no Q_det or Q_cross absorption",
        "accept": "Q_det and Q_cross cannot absorb missing holonomy, determinant, pressure, or anisotropic-stress transport terms.",
        "satisfied": False,
    },
    {
        "criterion": "Janus path-rule closure",
        "accept": "Janus source equations provide the path/family rule and its loop consistency proof.",
        "satisfied": False,
    },
]


def build_payload() -> dict:
    source_derived = all(row["satisfied"] for row in CRITERIA)
    return {
        "description": (
            "Bounded P0 criteria for holonomy loop consistency and source path-rule "
            "acceptance on the non-flat relative connection branch."
        ),
        "status": "criteria-open",
        "nonflat_relative_connection": True,
        "source_derived": source_derived,
        "physics_closed": False,
        "prediction_ready": False,
        "criteria": CRITERIA,
        "blockers": [
            "Janus has not yet provided a source-derived path/family rule",
            "loop constraints for R_Omega != 0 are not proved",
            "segmentation invariance for K and Q_cross is not proved",
        ],
        "verdict": (
            "For R_Omega != 0, path choice is physical. This branch remains "
            "source-derived False and prediction_ready False until Janus supplies "
            "the path rule, loop constraints, and shared K/Q_cross transport without "
            "lensing-fit or Q_det/Q_cross absorption shortcuts."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Holonomy Loop Consistency Criteria",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Non-flat relative connection: {payload['nonflat_relative_connection']}",
        f"Source derived: {payload['source_derived']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "| criterion | acceptance requirement | satisfied |",
        "|---|---|---|",
    ]
    for row in payload["criteria"]:
        lines.append(f"| {row['criterion']} | {row['accept']} | {row['satisfied']} |")
    lines.extend(["", "## Blockers", ""])
    lines.extend(f"- {item}" for item in payload["blockers"])
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
