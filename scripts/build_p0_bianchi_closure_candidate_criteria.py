from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_bianchi_closure_candidate_criteria.md")
JSON_PATH = Path("outputs/reports/p0_bianchi_closure_candidate_criteria.json")


CRITERIA = [
    {
        "criterion": "R_plus residual closure",
        "accept": "R_plus^mu=0 after substituting the candidate K_plus into the full positive-sector Bianchi residual.",
        "satisfied": False,
    },
    {
        "criterion": "R_minus residual closure",
        "accept": "R_minus^mu=0 after substituting the candidate K_minus into the full negative-sector Bianchi residual.",
        "satisfied": False,
    },
    {
        "criterion": "single L transport structure",
        "accept": "the same L_minus_to_plus/L_plus_to_minus maps are used by Bianchi K_plus/K_minus and optical Q_cross.",
        "satisfied": False,
    },
    {
        "criterion": "density determinant convention",
        "accept": "Q_det/proper-density/sign convention is fixed before residual or lensing normalization claims.",
        "satisfied": False,
    },
    {
        "criterion": "pressure and Pi divergence",
        "accept": "pressure and anisotropic-stress Pi divergence terms are included, not hidden in dust-only transport.",
        "satisfied": False,
    },
    {
        "criterion": "no fitted parameters",
        "accept": "closure follows from source equations with no fitted amplitudes, switches, or survey-tuned constants.",
        "satisfied": False,
    },
    {
        "criterion": "Newtonian and TOV limits",
        "accept": "the candidate recovers the accepted Newtonian weak-field and TOV/static-fluid limits.",
        "satisfied": False,
    },
    {
        "criterion": "accepted-source traceability",
        "accept": "each equation and convention is traceable to accepted source anchors or explicitly marked as derived.",
        "satisfied": False,
    },
]


def build_payload() -> dict:
    prediction_ready = all(row["satisfied"] for row in CRITERIA)
    return {
        "description": "Bounded P0 acceptance criteria for a Bianchi closure candidate.",
        "status": "criteria-open",
        "criteria": CRITERIA,
        "all_criteria_true": prediction_ready,
        "prediction_ready": prediction_ready,
        "reject_reasons": [
            "reject candidates that only close FLRW symmetry-reduced residuals",
            "reject candidates that only recover Newtonian weak-field behavior",
            "reject candidates that close dust while omitting pressure or Pi divergence",
            "reject candidates that use different L maps for K transport and Q_cross",
        ],
        "verdict": (
            "A Bianchi closure candidate is accepted only after every criterion is true; "
            "partial FLRW or Newtonian closure is not a prediction-ready result."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Bianchi Closure Candidate Criteria",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"All criteria true: {payload['all_criteria_true']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "| criterion | acceptance requirement | satisfied |",
        "|---|---|---|",
    ]
    for row in payload["criteria"]:
        lines.append(f"| {row['criterion']} | {row['accept']} | {row['satisfied']} |")
    lines.extend(["", "## Reject Reasons", ""])
    lines.extend(f"- {item}" for item in payload["reject_reasons"])
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
