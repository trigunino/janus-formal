from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_throat_radius_variational_equation_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_throat_radius_variational_equation_gate.json")


def build_payload() -> dict:
    declared = {
        "throat_radius_bibliography_checked": True,
        "topology_only_underdetermines_radius_law": True,
        "Sigma_boundary_action_available": True,
        "radial_embedding_variable_declared": True,
        "radial_Euler_Lagrange_equation_declared": True,
        "candidate_comoving_law_diagnostic_only": True,
        "observational_fit_forbidden": True,
    }
    equation = {
        "radial_Euler_Lagrange_operator_ready": True,
        "R_Sigma_equation_ready": True,
        "R_Sigma_equation_solved": False,
        "R_Sigma_of_a_ready": False,
    }
    effective_equation_terms = {
        "cartan_ghy_radial_term": "E_CartanGHY[R_Sigma,X_pm,K_pm](a)",
        "holst_nieh_yan_radial_term": "E_HolstNiehYan[R_Sigma,torsion](a)",
        "matter_flux_radial_term": "E_matterFlux[R_Sigma,F_a](a)",
        "counterterm_radial_term": "E_counterterm[R_Sigma,omega,e](a)",
    }
    effective_equation = (
        "E_RSigma(a) := E_CartanGHY(a) + E_HolstNiehYan(a) "
        "+ E_matterFlux(a) + E_counterterm(a) = 0"
    )
    return {
        "status": "janus-z2-sigma-throat-radius-variational-equation-gate",
        "active_core": "Z2_tunnel_Sigma",
        "primary_sources_checked": [
            "Petit/Margnat/Zejli 2024, arXiv:2412.04644",
            "La Camera 2011, arXiv:1102.5284",
            "Darmois-Israel dynamic thin-shell wormhole literature",
        ],
        "bibliography_result": (
            "No primary source gives the resolved Janus throat law. Generic FRW thin-shell "
            "work supplies candidate kinematics; the active law must come from the Sigma "
            "boundary action by varying the radial embedding."
        ),
        "declared": declared,
        "equation": equation,
        "variational_equation": (
            "E_RSigma(a) := delta S_Sigma[h(R_Sigma), K(R_Sigma), torsion(R_Sigma)] "
            "/ delta R_Sigma(a) = 0"
        ),
        "effective_RSigma_equation": effective_equation,
        "effective_RSigma_terms": effective_equation_terms,
        "effective_RSigma_equation_ready": all(effective_equation_terms.values()),
        "throat_radius_variational_problem_declared": all(declared.values()),
        "throat_radius_variational_equation_ready": all(declared.values())
        and equation["radial_Euler_Lagrange_operator_ready"]
        and equation["R_Sigma_equation_ready"],
        "throat_radius_variational_closure_ready": all(declared.values()) and all(equation.values()),
        "gate_passed": all(declared.values()) and all(equation.values()),
        "primary_blocker": (
            "none"
            if all(declared.values()) and all(equation.values())
            else "E_RSigma_equation_unsolved"
        ),
        "next_required": [
            "expand_E_RSigma_using_Cartan_GHY_Holst_matter_flux_junction_counterterm_blocks",
            "solve_E_RSigma_equals_zero_without_observational_fit",
            "propagate_solution_into_embedding_gauge_equations",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Throat Radius Variational Equation Gate",
        "",
        f"Active core: `{payload['active_core']}`",
        f"Equation ready: `{payload['throat_radius_variational_equation_ready']}`",
        f"Closure ready: `{payload['throat_radius_variational_closure_ready']}`",
        "",
        "## Variational Equation",
        f"`{payload['variational_equation']}`",
        "",
        "## Next Required",
    ]
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
