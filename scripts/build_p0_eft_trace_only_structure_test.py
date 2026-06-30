from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_eft_trace_only_structure_test.md")
JSON_PATH = Path("outputs/reports/p0_eft_trace_only_structure_test.json")


def build_payload() -> dict:
    generated_structures = {
        "trace_torsion_kinetic": True,
        "ricci_scalar_contacts": True,
        "ricci_tensor_contacts": True,
        "axial_torsion_sector": False,
        "epsilon_dual_curvature_sector": False,
        "nieh_yan_or_chiral_boundary_sector": False,
        "double_dual_horndeski_complete": False,
    }
    missing_for_closure = [
        "dual curvature contraction needed for full double-dual structure",
        "chiral/axial boundary sector needed for robust k4 completion",
        "spin-holonomy law if axial sector is to be Janus-derived",
    ]
    theorem_status = {
        "trace_only_structure_test_done": True,
        "trace_only_generates_basic_curvature_radion_terms": True,
        "trace_only_generates_double_dual": False,
        "trace_only_closes_k4": False,
        "spin_holonomy_branch_needed_if_no_other_source": True,
        "prediction_ready": False,
    }
    return {
        "description": "Structural test for the q_A=0, q_T=1 trace-only Dirac-Cartan EFT branch.",
        "status": "trace-only-structure-insufficient-for-double-dual",
        "theorem_status": theorem_status,
        "generated_structures": generated_structures,
        "missing_for_closure": missing_for_closure,
        "verdict": (
            "Trace torsion is a valid first branch and fixes q_T geometrically, but structurally "
            "it does not contain the axial/dual sector needed for the full double-dual closure."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 EFT Trace-Only Structure Test",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
    ]
    lines.extend(f"{key}: {value}" for key, value in payload["theorem_status"].items())
    lines.extend(["", "## Generated Structures"])
    for key, value in payload["generated_structures"].items():
        lines.append(f"- {key}: {value}")
    lines.extend(["", "## Missing For Closure"])
    lines.extend(f"- {item}" for item in payload["missing_for_closure"])
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
