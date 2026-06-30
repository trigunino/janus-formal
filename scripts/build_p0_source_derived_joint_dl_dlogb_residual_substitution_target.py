from __future__ import annotations

from pathlib import Path
import json
import sys


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_janus_source_residual_closure_obligation_matrix import (
    build_payload as build_source_matrix,
)


REPORT_PATH = Path("outputs/reports/p0_source_derived_joint_dl_dlogb_residual_substitution_target.md")
JSON_PATH = Path("outputs/reports/p0_source_derived_joint_dl_dlogb_residual_substitution_target.json")


def _joint_row(sector: str, matrix: dict) -> dict:
    identities = matrix["identity_status"]
    required = [
        "same_l_dl_source_law",
        "b4vol_source_measure_law",
        "falpha_source_law",
        "projected_cuu_force_balance",
    ]
    source_derived = all(identities[name]["source_derived"] for name in required)
    return {
        "sector": sector,
        "substitution_target": f"{sector}=0 after one same-L/DL law and one B_4vol measure law",
        "required_identities": required,
        "same_l_usage": ["K_plus/K_minus", "Q_cross optical projection", "kinetic/Vlasov projection"],
        "phase_space_requirements": [
            "B_4vol source measure",
            "Q_det convention kept separate from Q_cross",
            "diagnostic Vlasov not promoted to physical closure",
        ],
        "source_derived": source_derived,
        "closed": bool(source_derived and matrix["all_guardrails_satisfied"]),
    }


def build_payload() -> dict:
    matrix = build_source_matrix()
    residual_substitution_rows = [
        _joint_row("R_plus", matrix),
        _joint_row("R_minus", matrix),
    ]
    forbidden_shortcuts = [
        "no scalar Q_det absorption of D L or pressure/tensor terms",
        "no scalar Q_cross absorption of transport/product-rule terms",
        "no independent optical L distinct from K and kinetic L",
        "no fitted Omega or observational normalization",
        "no Vlasov diagnostic promotion before phase-space measure closure",
    ]
    return {
        "description": "Joint source-derived target for substituting D L and D log B_4vol into R_plus/R_minus.",
        "status": "source-derived-joint-dl-dlogb-residual-substitution-target-open",
        "source_matrix_status": matrix["status"],
        "residual_substitution_rows": residual_substitution_rows,
        "forbidden_shortcuts": forbidden_shortcuts,
        "all_rows_source_derived": all(row["source_derived"] for row in residual_substitution_rows),
        "all_rows_closed": all(row["closed"] for row in residual_substitution_rows),
        "uses_observational_fit": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "This target binds D L, DlogB4vol, Falpha and Cuu into both residual rows. "
            "It stays open until the source residual obligation matrix closes."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Source-Derived Joint DL/DlogB Residual Substitution Target",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Source matrix status: {payload['source_matrix_status']}",
        f"All rows source-derived: {payload['all_rows_source_derived']}",
        f"All rows closed: {payload['all_rows_closed']}",
        f"Uses observational fit: {payload['uses_observational_fit']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Residual Substitution Rows",
        "",
        "| sector | target | identities | same-L usage | phase-space requirements | closed |",
        "|---|---|---|---|---|---:|",
    ]
    for row in payload["residual_substitution_rows"]:
        lines.append(
            f"| {row['sector']} | {row['substitution_target']} | "
            f"{'; '.join(row['required_identities'])} | "
            f"{'; '.join(row['same_l_usage'])} | "
            f"{'; '.join(row['phase_space_requirements'])} | {row['closed']} |"
        )
    lines.extend(["", "## Forbidden Shortcuts", ""])
    lines.extend(f"- {item}" for item in payload["forbidden_shortcuts"])
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
