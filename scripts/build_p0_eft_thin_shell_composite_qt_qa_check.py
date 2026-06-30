from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_eft_thin_shell_composite_qt_qa_check.md")
JSON_PATH = Path("outputs/reports/p0_eft_thin_shell_composite_qt_qa_check.json")


def build_payload() -> dict:
    matrix_model = {
        "basis": "I and C=gamma^n gamma5 with C^2=1",
        "jump_matrix": "M(q_T,q_A)=4*q_T*I - 2*q_A*C",
        "trace_only": "q_A=0 gives M proportional to I, so no chiral sorting",
        "composite": "q_A != 0 activates the C eigenspace split",
    }
    projector_check = {
        "surface_operator": "P = a*I + b*C",
        "idempotence_equations": "P^2=P gives a^2+b^2=a and 2ab=b",
        "nontrivial_projectors": "a=1/2 and b=+/-1/2",
        "required_normalized_form": "P_chiral=(1 +/- C)/2",
        "raw_M_status": "M is not automatically idempotent before normalization",
        "ratio_status": "q_A/q_T must be fixed by shell normalization or Pin holonomy, not by trace torsion alone",
    }
    pin_minus_candidate = {
        "q_T": "1",
        "q_A": "sign(Sigma)/sqrt(6)",
        "effect": "adds the chiral Clifford generator but does not by itself prove projector normalization",
        "remaining_bridge": "derive shell normalization mapping M(q_T,q_A) to P_chiral",
    }
    theorem_status = {
        "composite_qt_qa_loaded": True,
        "trace_only_no_go_confirmed": True,
        "chiral_clifford_generator_present_if_qA_nonzero": True,
        "idempotence_conditions_derived": True,
        "pin_minus_qA_candidate_recorded": True,
        "projector_normalization_derived_from_janus": False,
        "aps_domain_preserved": False,
        "prediction_ready": False,
    }
    obligations = [
        "derive the shell normalization that turns M(q_T,q_A) into P_chiral",
        "show Pin- holonomy fixes q_A/q_T with the required sign",
        "prove the normalized operator satisfies P^2=P",
        "then connect the chiral eigenspace to APS domain preservation",
    ]
    return {
        "description": "Composite q_T/q_A thin-shell check for chiral boundary projector formation.",
        "status": "composite-clifford-projector-open",
        "matrix_model": matrix_model,
        "projector_check": projector_check,
        "pin_minus_candidate": pin_minus_candidate,
        "theorem_status": theorem_status,
        "obligations": obligations,
        "verdict": (
            "The axial term supplies the required gamma^n gamma5 splitting. The remaining "
            "gap is projector normalization from Janus shell geometry or Pin holonomy."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 EFT Thin-Shell Composite qT/qA Check",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        "",
        "## Matrix Model",
    ]
    lines.extend(f"- {key}: {value}" for key, value in payload["matrix_model"].items())
    lines.extend(["", "## Projector Check"])
    lines.extend(f"- {key}: {value}" for key, value in payload["projector_check"].items())
    lines.extend(["", "## Pin- Candidate"])
    lines.extend(f"- {key}: {value}" for key, value in payload["pin_minus_candidate"].items())
    lines.extend(["", "## Status"])
    lines.extend(f"- {key}: {value}" for key, value in payload["theorem_status"].items())
    lines.extend(["", "## Obligations"])
    lines.extend(f"- {item}" for item in payload["obligations"])
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
