from __future__ import annotations

from pathlib import Path
import json
import sys


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_orbifold_pt_action_variation_gate import build_payload as build_action_gate


REPORT_PATH = Path("outputs/reports/p0_orbifold_pt_source_current_gate.md")
JSON_PATH = Path("outputs/reports/p0_orbifold_pt_source_current_gate.json")


def build_payload() -> dict:
    action = build_action_gate()
    source_rows = [
        {
            "source": "defect_curvature_jump",
            "candidate": "J_defect ~ [*F_PT]_{Sigma_PT}",
            "covariant": True,
            "pt_compatible": True,
            "source_derived": False,
            "accepted": False,
            "blocker": "Sigma_PT matching law is written separately but B_defect/S_defect is not derived",
        },
        {
            "source": "defect_tension_current",
            "candidate": "J_defect ~ delta B_defect/delta A_PT",
            "covariant": True,
            "pt_compatible": True,
            "source_derived": False,
            "accepted": False,
            "blocker": "B_defect is not derived from Janus/PT geometry",
        },
        {
            "source": "matter_solder_torque",
            "candidate": "J_matter ~ P_so(1,3)(T_plus L_gamma T_minus L_gamma^T)",
            "covariant": True,
            "pt_compatible": True,
            "source_derived": False,
            "accepted": False,
            "blocker": "pressure/Pi and Vlasov moment transport remain open",
        },
        {
            "source": "vlasov_phase_space_current",
            "candidate": "J_matter ~ integral p wedge D_A f over mass shell",
            "covariant": True,
            "pt_compatible": True,
            "source_derived": False,
            "accepted": False,
            "blocker": "requires full Janus two-sector Vlasov action/measure",
        },
        {
            "source": "observable_residual_current",
            "candidate": "J ~ fitted lensing/growth residual",
            "covariant": False,
            "pt_compatible": False,
            "source_derived": False,
            "accepted": False,
            "blocker": "observational fit is forbidden",
        },
    ]
    accepted_rows = [row["source"] for row in source_rows if row["accepted"]]
    admissible_unaccepted = [
        row["source"]
        for row in source_rows
        if row["covariant"] and row["pt_compatible"] and not row["accepted"]
    ]
    return {
        "description": (
            "Gate for admissible source currents in the orbifold/PT solder equation "
            "D_A *F_PT = J_defect + J_matter."
        ),
        "status": "orbifold-pt-source-current-gate-open",
        "depends_on": ["p0_orbifold_pt_action_variation_gate"],
        "action_gate_status": action["status"],
        "source_rows": source_rows,
        "accepted_source_currents": accepted_rows,
        "admissible_but_unaccepted_sources": admissible_unaccepted,
        "current_equation": "D_A *F_PT = J_defect + J_matter",
        "covariant_current_candidates_written": True,
        "defect_current_source_derived": False,
        "matter_current_source_derived": False,
        "observable_fit_current_rejected": True,
        "unique_current_selected": False,
        "a_pt_euler_equation_closed": False,
        "uses_observational_fit": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "Several covariant PT-compatible current shapes exist, but none is accepted "
            "until an orbifold defect law or two-sector matter/Vlasov action derives it. "
            "The fitted-observable current is explicitly rejected."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Orbifold/PT Source Current Gate",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Current equation: `{payload['current_equation']}`",
        f"Covariant current candidates written: {payload['covariant_current_candidates_written']}",
        f"Defect current source-derived: {payload['defect_current_source_derived']}",
        f"Matter current source-derived: {payload['matter_current_source_derived']}",
        f"Observable fit current rejected: {payload['observable_fit_current_rejected']}",
        f"Unique current selected: {payload['unique_current_selected']}",
        f"A_PT Euler equation closed: {payload['a_pt_euler_equation_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "| source | candidate | covariant | PT-compatible | source-derived | accepted | blocker |",
        "|---|---|---:|---:|---:|---:|---|",
    ]
    for row in payload["source_rows"]:
        lines.append(
            f"| {row['source']} | `{row['candidate']}` | {row['covariant']} | "
            f"{row['pt_compatible']} | {row['source_derived']} | "
            f"{row['accepted']} | {row['blocker']} |"
        )
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
