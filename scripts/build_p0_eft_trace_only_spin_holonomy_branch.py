from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_eft_trace_only_spin_holonomy_branch.md")
JSON_PATH = Path("outputs/reports/p0_eft_trace_only_spin_holonomy_branch.json")


def build_payload() -> dict:
    trace_only_branch = {
        "id": "R_trace_only",
        "condition": "q_A = 0, q_T = 1",
        "janus_geometric_status": "q_T fixed by solder-volume conservation",
        "expected_bulk_terms": ["(nabla chi)^2", "(nabla chi)^4", "Ricci trace contacts"],
        "expected_missing_terms": ["dual curvature contraction", "full double-dual Horndeski structure", "k4 boundary completion"],
        "predicted_to_close_required_deltaN": False,
        "actual_heat_kernel_computed": False,
    }
    spin_holonomy_branch = {
        "id": "R_paired_axial_trace",
        "condition": "q_T = 1, q_A = sign(Sigma)/sqrt(6)",
        "geometric_claim": "Janus PT mirror acts as chiral spin-holonomy around the orbifold defect",
        "why_not_free_fit": "q_A is fixed by canonical spin-holonomy normalization, not by observations",
        "still_to_prove": [
            "derive the PT/chirality jump from the Janus spin connection",
            "show odd axial residues cancel between sheets",
            "compute Dirac-Cartan a4 with paired axial trace torsion",
            "verify double-dual/Horndeski coefficient and k4 boundary completion",
        ],
        "source_derived_from_published_janus": False,
    }
    theorem_status = {
        "trace_only_branch_ready_to_test": True,
        "trace_only_expected_sufficient": False,
        "spin_holonomy_contingency_written": True,
        "q_T_fixed": True,
        "q_A_fixed_conditionally": True,
        "pt_spin_holonomy_proved": False,
        "heat_kernel_computed": False,
        "prediction_ready": False,
    }
    return {
        "description": "Trace-only torsion test and PT spin-holonomy contingency for the Dirac-Cartan EFT route.",
        "status": "trace-only-first-spin-holonomy-contingency-open",
        "theorem_status": theorem_status,
        "trace_only_branch": trace_only_branch,
        "spin_holonomy_branch": spin_holonomy_branch,
        "next_steps": [
            "run symbolic structure test for q_A=0, q_T=1",
            "if trace-only cannot generate double-dual, derive PT spin-holonomy from the orbifold spin connection",
            "only then run q_A=sign(Sigma)/sqrt(6), q_T=1 heat-kernel target",
        ],
        "verdict": (
            "The tactical order is clear: test trace torsion first. If it fails, the next non-free "
            "route is a Janus PT/chiral spin-holonomy law fixing q_A."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 EFT Trace-Only and Spin-Holonomy Branch",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
    ]
    lines.extend(f"{key}: {value}" for key, value in payload["theorem_status"].items())
    lines.extend(["", "## Trace-Only Branch"])
    for key, value in payload["trace_only_branch"].items():
        lines.append(f"- {key}: {value}")
    lines.extend(["", "## Spin-Holonomy Contingency"])
    for key, value in payload["spin_holonomy_branch"].items():
        lines.append(f"- {key}: {value}")
    lines.extend(["", "## Next Steps"])
    lines.extend(f"- {item}" for item in payload["next_steps"])
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
