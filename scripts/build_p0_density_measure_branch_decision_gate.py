from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_density_measure_branch_decision_gate.md")
JSON_PATH = Path("outputs/reports/p0_density_measure_branch_decision_gate.json")


def build_payload() -> dict:
    branches = [
        {
            "branch": "field_equation_4volume",
            "uses": "B_4vol=sqrt(-g_other)/sqrt(-g_self)",
            "needs": "lapse and determinant convention from source equations",
            "accepted": False,
        },
        {
            "branch": "dust_flux_3volume",
            "uses": "J_phi or spatial dust-volume Jacobian",
            "needs": "lift to 4D field equations without dropping lapse",
            "accepted": False,
        },
        {
            "branch": "effective_density_absorbs_B",
            "uses": "rho_eff=B rho_to",
            "needs": "no second Q_det multiplication",
            "accepted": False,
        },
    ]
    acceptance = [
        "one branch selected before residual substitution",
        "B/J_phi relation proven for the selected branch",
        "Q_det used only as density/volume map",
        "Q_cross kept as optical projection only",
        "D_receiver(B rho_to u_to)=0 proven or left open",
    ]
    return {
        "description": "Decision gate for selecting the density-measure branch in D_phi/DlogB cancellation.",
        "status": "density-measure-branch-decision-open",
        "branches": branches,
        "acceptance": acceptance,
        "selected_branch": None,
        "branch_decision_closed": False,
        "effective_density_continuity_closed": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "The D_phi/DlogB proof cannot close until exactly one density-measure "
            "branch is selected and its B/J_phi/Q_det identities are source-derived."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Density Measure Branch Decision Gate",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Selected branch: {payload['selected_branch']}",
        f"Branch decision closed: {payload['branch_decision_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "| branch | uses | needs | accepted |",
        "|---|---|---|---|",
    ]
    for row in payload["branches"]:
        lines.append(f"| {row['branch']} | {row['uses']} | {row['needs']} | {row['accepted']} |")
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
