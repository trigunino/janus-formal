from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_falpha_flow_projected_dl_residual_substitution.md")
JSON_PATH = Path("outputs/reports/p0_falpha_flow_projected_dl_residual_substitution.json")


def build_payload() -> dict:
    substitution_checks = [
        {
            "sector": "plus",
            "dl_row": "D_L transported tetrad/velocity terms in D_plus K_minus_to_plus",
            "substitution": "D_self L=F_alpha L with flow-projected F_minus_to_plus",
            "result": "D_L row reduced conditionally",
            "closed": False,
        },
        {
            "sector": "minus",
            "dl_row": "D_L transported tetrad/velocity terms in D_minus K_plus_to_minus",
            "substitution": "D_self L^{-1}=F_alpha L^{-1} with mirror flow projection",
            "result": "D_L row reduced conditionally",
            "closed": False,
        },
    ]
    still_open = [
        "F_alpha is minimal-gauge candidate, not source-derived",
        "same-L K/Q_cross compatibility remains open",
        "Cuu/projected force balance remains open until hE=rho hCuu is action-derived",
        "DlogB and D_phi measure rows are separate",
    ]
    return {
        "description": "Flow-projected F_alpha substitution test for D_L residual rows.",
        "status": "flow-projected-dl-substitution-open",
        "substitution_checks": substitution_checks,
        "still_open": still_open,
        "dl_rows_reduced_conditionally": True,
        "falpha_source_derived": False,
        "connection_force_closed": False,
        "r_plus_closed": False,
        "r_minus_closed": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "Flow-projected F_alpha can reduce the D_L rows conditionally. It does not "
            "close Cuu, DlogB, D_phi, same-L, or prediction readiness."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Falpha Flow-projected DL Residual Substitution",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"DL rows reduced conditionally: {payload['dl_rows_reduced_conditionally']}",
        f"Falpha source-derived: {payload['falpha_source_derived']}",
        f"Connection force closed: {payload['connection_force_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Substitution Checks",
        "",
    ]
    for row in payload["substitution_checks"]:
        lines.append(f"- {row['sector']}: {row['dl_row']}")
        lines.append(f"  - substitution: `{row['substitution']}`")
        lines.append(f"  - result: {row['result']}")
        lines.append(f"  - closed: {row['closed']}")
    lines.extend(["", "## Still Open", ""])
    lines.extend(f"- {item}" for item in payload["still_open"])
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
