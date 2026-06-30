from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_residual_zero_condition_matrix.md")
JSON_PATH = Path("outputs/reports/p0_residual_zero_condition_matrix.json")


def build_payload() -> dict:
    rows = [
        {
            "branch": "field_equation_4volume_source",
            "must_zero": [
                "D_plus log B_4vol_plus_from_minus terms",
                "D_minus log B_4vol_minus_from_plus terms",
                "D L_minus_to_plus terms",
                "D L_plus_to_minus terms",
                "connection-difference force terms",
            ],
            "missing_proof": "Janus source equations must provide B_4vol and D L cancellation identities",
            "passes": False,
        },
        {
            "branch": "slice_dust_flux_source",
            "must_zero": [
                "D log V3_dust terms",
                "lapse reinsertion residual",
                "slice projector derivative terms",
                "D L terms",
            ],
            "missing_proof": "spatial dust flux must be lifted to 4D field equations without dropping lapse terms",
            "passes": False,
        },
        {
            "branch": "effective_density_source",
            "must_zero": [
                "D rho_eff absorbed-measure terms",
                "undocumented Q_det reuse",
                "transported force residual",
                "D L terms",
            ],
            "missing_proof": "rho_eff must define exactly one absorbed measure and close both residuals",
            "passes": False,
        },
    ]
    global_requirements = [
        "R_plus=0",
        "R_minus=0",
        "single L structure for K and Q_cross",
        "no scalar absorption of pressure or Pi",
        "accepted-paper source traceability",
    ]
    return {
        "description": "P0 pass/fail matrix for residual zero conditions after source-measure substitution.",
        "status": "zero-condition-matrix-open",
        "matrix_written": True,
        "any_branch_passes": False,
        "accepted_branch": None,
        "r_plus_closed": False,
        "r_minus_closed": False,
        "physics_closed": False,
        "prediction_ready": False,
        "rows": rows,
        "global_requirements": global_requirements,
        "verdict": (
            "All current branches fail as proofs because required zero identities are still missing. "
            "This is a rigorous rejection state, not a numerical tuning problem."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Residual Zero Condition Matrix",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Any branch passes: {payload['any_branch_passes']}",
        f"Accepted branch: {payload['accepted_branch']}",
        f"R_plus closed: {payload['r_plus_closed']}",
        f"R_minus closed: {payload['r_minus_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "| branch | must zero | missing proof | passes |",
        "|---|---|---|---|",
    ]
    for row in payload["rows"]:
        lines.append(
            f"| {row['branch']} | {'; '.join(row['must_zero'])} | {row['missing_proof']} | {row['passes']} |"
        )
    lines.extend(["", "## Global Requirements", ""])
    lines.extend(f"- {item}" for item in payload["global_requirements"])
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
