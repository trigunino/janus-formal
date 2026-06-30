from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_eft_radion_boundary_source_kick.md")
JSON_PATH = Path("outputs/reports/p0_eft_radion_boundary_source_kick.json")


def build_payload() -> dict:
    source = {
        "definition": "Source_chi_boundary = - delta S_boundary / delta chi",
        "jump_variable": "Delta_chi",
        "volume_term": "d(lambda*Delta_chi)/dDelta_chi = lambda = -4*q_T",
        "nieh_yan_term": "d(kappa)/dDelta_chi = 2*q_A when kappa=2*q_A*Delta_chi",
        "cartan_ghy_response": (
            "d(beta*Delta_chi)/dDelta_chi = 0 when "
            "beta*Delta_chi=-sigma*(1+tau)/2 is imposed as a response product"
        ),
        "cartan_ghy_constant_beta_branch": (
            "If beta is varied as a constant first, the source is beta and the branch "
            "reopens a non-geometric normalization."
        ),
    }
    kick = {
        "kg_x_jump": "chi_x(+)-chi_x(-)=I_chi/(H_Sigma^2)",
        "I_chi_response_branch": "4*q_T - 2*q_A plus orientation/sign convention of the boundary normal",
        "Omega_T_after_kick": "Omega_T(a_Sigma+)=(chi_x(-)+I_chi/H_Sigma^2)^2/(3*M_pl^2)",
        "use_in_growth": "replace the empirical Omega_T family by the integrated chi(x) trajectory",
    }
    theorem_status = {
        "source_defined_as_boundary_variation": True,
        "lambda_source_closed": True,
        "kappa_source_closed_conditionally": True,
        "beta_response_product_has_no_local_radion_force": True,
        "beta_constant_branch_rejected_for_no_fit": True,
        "source_kick_structured": True,
        "potential_V_fixed_from_Janus_action": False,
        "Omega_T_no_fit_ready": False,
    }
    obligations = [
        "fix the global orientation/sign convention in I_chi",
        "derive V(chi) from the same Janus-Cartan action",
        "integrate chi(x) with the boundary kick and export Omega_T(a)",
    ]
    return {
        "description": "Boundary variational source for the radion KG background.",
        "status": "source-kick-structured-potential-open",
        "source": source,
        "kick": kick,
        "theorem_status": theorem_status,
        "obligations": obligations,
        "verdict": (
            "The radion boundary source is now sourced as a functional derivative of the RUN 1 "
            "surface action. The no-fit path still needs the bulk potential V(chi), but the "
            "spinor/boundary source is no longer a free profile."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 EFT Radion Boundary Source Kick",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        "",
        "## Source",
    ]
    lines.extend(f"- {key}: {value}" for key, value in payload["source"].items())
    lines.extend(["", "## Kick"])
    lines.extend(f"- {key}: {value}" for key, value in payload["kick"].items())
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
