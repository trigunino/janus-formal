from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_eft_thin_shell_jump_symbolic_check.md")
JSON_PATH = Path("outputs/reports/p0_eft_thin_shell_jump_symbolic_check.json")


def build_payload() -> dict:
    derivation = {
        "normal_coordinate": "n with Sigma at n=0",
        "radion_profile": "chi(n)=chi_- + Delta_chi * Theta(n)",
        "trace_torsion": "T_mu = q_T partial_mu chi, q_T=1",
        "shell_term": "T_n = Delta_chi * delta(n)",
        "integrated_dirac_form": "gamma^n [psi]_minus_plus + Delta_chi * M_T psi|_Sigma = 0",
        "jump_condition": "[psi] = -Delta_chi * (gamma^n)^-1 M_T psi|_Sigma",
    }
    algebraic_check = {
        "candidate_matrix": "J_shell = (gamma^n)^-1 M_T",
        "chiral_projector_form": "P_chiral=(1 +/- gamma5)/2",
        "projector_required": "J_shell must be proportional to gamma5 with eigenvalue constraint",
        "thin_shell_result": "trace torsion alone gives a jump matrix, not an automatic chiral projector",
        "missing_condition": "need M_T proportional to gamma^n gamma5 or an axial/torsion-boundary term",
    }
    theorem_status = {
        "thin_shell_delta_integrated": True,
        "spinor_jump_condition_derived": True,
        "chiral_projector_derived_from_trace_torsion_alone": False,
        "requires_axial_or_boundary_clifford_factor": True,
        "aps_domain_preserved": False,
        "prediction_ready": False,
    }
    obligations = [
        "derive the exact Clifford matrix M_T for the Janus trace torsion coupling",
        "check whether M_T contains gamma^n gamma5 from Cartan/Pin geometry",
        "if M_T is identity-like, record no-go for trace torsion alone",
        "if M_T is gamma^n gamma5-like, derive the chiral projector and APS preservation",
    ]
    return {
        "description": "Symbolic thin-shell check for whether q_T=1 trace torsion forces a chiral boundary projector.",
        "status": "thin-shell-jump-derived-projector-open",
        "derivation": derivation,
        "algebraic_check": algebraic_check,
        "theorem_status": theorem_status,
        "obligations": obligations,
        "verdict": (
            "The thin-shell integration gives a spinor jump condition, but trace torsion alone "
            "does not yet force the chiral projector. The remaining question is the Clifford "
            "matrix carried by the Janus Cartan/Pin shell coupling."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 EFT Thin-Shell Jump Symbolic Check",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        "",
        "## Derivation",
    ]
    lines.extend(f"- {key}: {value}" for key, value in payload["derivation"].items())
    lines.extend(["", "## Algebraic Check"])
    lines.extend(f"- {key}: {value}" for key, value in payload["algebraic_check"].items())
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
