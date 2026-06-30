from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_eft_boundary_dirac_projector_el.md")
JSON_PATH = Path("outputs/reports/p0_eft_boundary_dirac_projector_el.json")


def build_payload() -> dict:
    boundary_action = {
        "bulk_surface_variation": "delta S_bulk|_Sigma gives a normal Dirac flux term",
        "dirac_boundary_term": "S_bnd=(i/2) int_Sigma sqrt(-h) bar(psi) gamma^n psi",
        "janus_inputs": "tetrad sign transition, Pin- axial shell term, q_T=1 trace shell",
        "euler_lagrange_target": "delta S_total / delta bar(psi)|_Sigma = 0",
    }
    projector_derivation = {
        "boundary_equation_form": "gamma^n (I +/- gamma^n gamma5) psi|_Sigma = 0",
        "clifford_reduction": "left multiplication by gamma^n reduces this to (I -/+ gamma5) psi|_Sigma = 0",
        "projector": "P_chiral=(I -/+ gamma5)/2",
        "cayley_relation": "Cayley remains a transition map; the projector comes from boundary EL constraints",
    }
    theorem_status = {
        "boundary_dirac_term_identified": True,
        "bulk_surface_variation_identified": True,
        "boundary_el_route_encoded": True,
        "cayley_no_go_preserved": True,
        "projector_from_boundary_el_conditionally": True,
        "janus_coefficients_make_factorization_proved": False,
        "aps_domain_preserved": False,
        "prediction_ready": False,
    }
    obligations = [
        "derive the exact coefficient of the Pin-/axial shell term in the boundary EL equation",
        "derive the exact coefficient of the trace shell term in the boundary EL equation",
        "prove those coefficients factor as gamma^n(I +/- gamma^n gamma5)",
        "prove the resulting chiral projector is equivalent to the APS domain used in the eta argument",
    ]
    return {
        "description": "Boundary Euler-Lagrange route for deriving the chiral spinor projector.",
        "status": "boundary-el-projector-conditional",
        "boundary_action": boundary_action,
        "projector_derivation": projector_derivation,
        "theorem_status": theorem_status,
        "obligations": obligations,
        "verdict": (
            "The correct route around the finite-Cayley obstruction is a boundary Euler-Lagrange "
            "constraint. The remaining proof is coefficient factorization from Janus/Pin geometry."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 EFT Boundary Dirac Projector EL",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        "",
        "## Boundary Action",
    ]
    lines.extend(f"- {key}: {value}" for key, value in payload["boundary_action"].items())
    lines.extend(["", "## Projector Derivation"])
    lines.extend(f"- {key}: {value}" for key, value in payload["projector_derivation"].items())
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
