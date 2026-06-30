from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_b_jphi_qdet_source_measure_branch_selection_target.md")
JSON_PATH = Path("outputs/reports/p0_b_jphi_qdet_source_measure_branch_selection_target.json")


def build_payload() -> dict:
    branches = [
        {
            "branch": "field_equation_4volume_source",
            "measure": "B_4vol rho_to",
            "status": "candidate-open",
        },
        {
            "branch": "slice_dust_flux_source",
            "measure": "V3_dust rho_to",
            "status": "candidate-open",
        },
        {
            "branch": "effective_density_source",
            "measure": "rho_eff with Q_det already absorbed",
            "status": "candidate-open",
        },
    ]
    acceptance = [
        "exactly one active convention",
        "no Q_det double count after convention selection",
        "Q_cross remains optical and separate",
        "lapse/slice terms accounted",
        "D_receiver(B rho_to u_to)=0 closed or explicitly blocked",
        "Bianchi residual substitution rerun after selection",
    ]
    return {
        "description": "Source-measure branch selection target for B/J_phi/Q_det.",
        "status": "source-measure-branch-selection-open",
        "branches": branches,
        "acceptance": acceptance,
        "selected_branch": None,
        "source_traceability_closed": False,
        "lapse_slice_closed": False,
        "bianchi_after_selection_closed": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "B/J_phi/Q_det can close only after one source-measure branch is selected "
            "from Janus equations and reinserted into the Bianchi residuals."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 B/J_phi/Q_det Source Measure Branch Selection Target",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Selected branch: {payload['selected_branch']}",
        f"Source traceability closed: {payload['source_traceability_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "| branch | measure | status |",
        "|---|---|---|",
    ]
    for row in payload["branches"]:
        lines.append(f"| {row['branch']} | {row['measure']} | {row['status']} |")
    lines.extend(["", "## Acceptance", ""])
    lines.extend(f"- {item}" for item in payload["acceptance"])
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
