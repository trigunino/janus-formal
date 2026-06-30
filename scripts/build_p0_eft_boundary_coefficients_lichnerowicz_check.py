from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_eft_boundary_coefficients_lichnerowicz_check.md")
JSON_PATH = Path("outputs/reports/p0_eft_boundary_coefficients_lichnerowicz_check.json")


def build_payload() -> dict:
    candidate_run1 = {
        "input": (
            "M_bulk=(i/2)N, M_bnd=tau*(i/2)N, "
            "M_janus=i*(4*q_T*I - 2*q_A*C)*Delta_chi"
        ),
        "basis": "I, N=gamma^n, G=gamma5, C=gamma^n gamma5",
        "coefficients_without_common_i": {
            "m_I": "4*q_T*Delta_chi",
            "m_N": "(1+tau)/2",
            "m_G": "0",
            "m_C": "-2*q_A*Delta_chi",
        },
        "factorization_conditions": "m_I=0, m_C=0, m_G=sigma*eps_n*m_N",
        "literal_verdict": (
            "The literal source dictionary fails RUN 1 unless Delta_chi=0 or extra "
            "derived boundary pieces cancel m_I and m_C and rotate the axial source into m_G."
        ),
    }
    run1 = {
        "basis": "M_tot = m_I*I + m_N*gamma^n + m_G*gamma5 + m_C*gamma^n gamma5",
        "bulk_flux": "contributes only to m_N",
        "dirac_boundary_term": "renormalizes m_N with orientation sign",
        "janus_pin_shell": "must contribute only to m_G after trace pieces cancel",
        "target_conditions": "m_I=0, m_C=0, m_G=sigma*eps_n*m_N",
        "candidate_closure": "coefficient matching is closed only if Janus/Pin shell fixes the m_G/m_N ratio",
    }
    run2 = {
        "aps_boundary_type": "Riemannian compact APS boundary or Wick-rotated dS3 slice",
        "lichnerowicz": "D_Sigma^2 = nabla^*nabla + R_Sigma/4",
        "curvature": "R_Sigma=6H^2 gives R_Sigma/4=3H^2/2 > 0",
        "zero_mode_result": "ker(D_Sigma)=0 if H^2>0 and the APS boundary is Riemannian compact",
        "lorentzian_caveat": "raw Lorentzian dS3 needs a separate spectral-domain definition",
    }
    theorem_status = {
        "run1_physical_slots_defined": True,
        "run1_matching_equation_ready": True,
        "run1_literal_candidate_evaluated": True,
        "run1_literal_candidate_matches": False,
        "run1_requires_extra_derived_boundary_cancellation": True,
        "run1_matching_proved_from_janus_coefficients": False,
        "run2_lichnerowicz_zero_mode_argument_encoded": True,
        "run2_zero_modes_absent_on_riemannian_compact_boundary": True,
        "run2_lorentzian_dS3_spectrum_defined": False,
        "prediction_ready": False,
    }
    obligations = [
        "derive cancellation of the literal m_I trace residue or record a no-go",
        "derive cancellation of the literal m_C residue or record a no-go",
        "derive a boundary Clifford rotation/projection that converts the axial shell contribution into m_G",
        "then prove m_G=sigma*eps_n*m_N with no free normalization",
        "choose or derive the Riemannian APS boundary used for the eta invariant",
    ]
    return {
        "description": "Boundary coefficient slots and Lichnerowicz zero-mode check for RUN 1/RUN 2.",
        "status": "zero-modes-closed-conditionally-literal-run1-fails",
        "candidate_run1": candidate_run1,
        "run1": run1,
        "run2": run2,
        "theorem_status": theorem_status,
        "obligations": obligations,
        "verdict": (
            "RUN 2 zero modes close on a compact Riemannian APS boundary with H^2>0. "
            "The literal RUN 1 coefficient dictionary fails because it leaves I and C residues. "
            "Janus must derive extra boundary cancellation/rotation before the m_G/m_N test can pass."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 EFT Boundary Coefficients Lichnerowicz Check",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        "",
        "## RUN 1",
    ]
    lines.extend(f"- {key}: {value}" for key, value in payload["candidate_run1"].items())
    lines.extend(["", "## RUN 1 Slots"])
    lines.extend(f"- {key}: {value}" for key, value in payload["run1"].items())
    lines.extend(["", "## RUN 2"])
    lines.extend(f"- {key}: {value}" for key, value in payload["run2"].items())
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
