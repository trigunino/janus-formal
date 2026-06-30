from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_non_rustine_closure_research_kernel.md")
JSON_PATH = Path("outputs/reports/p0_non_rustine_closure_research_kernel.json")


def build_payload() -> dict:
    distinction = {
        "allowed_selection": (
            "Choose a branch only when it is forced by a published Janus source, "
            "a variational principle, a symmetry/Noether identity, stability, or a "
            "well-posed boundary/gauge condition stated before observational comparison."
        ),
        "forbidden_choice": (
            "Choose S_cross, Phi_R, L, Q_det or Q_cross freely because it makes "
            "R_plus/R_minus vanish or improves data agreement."
        ),
    }
    pt_lie_assessment = [
        {
            "idea": "PT/Lie/Poincare inversion geometry",
            "useful_for": "restricting admissible maps phi and tetrad solder L",
            "not_enough_for": "unique dynamics unless it yields an action or independent field equations",
        },
        {
            "idea": "Janus symplectic/torsor group",
            "useful_for": "classifying energy, momentum and charge transformations",
            "not_enough_for": "K_plus/K_minus and Q_cross unless the group action becomes a variational coupling",
        },
        {
            "idea": "transition/solder geometry between sectors",
            "useful_for": "making phi, J_phi, L and Omega geometrical rather than fitted scalars",
            "not_enough_for": "prediction unless Noether split and matter transport close",
        },
    ]
    closure_routes = [
        {
            "route": "source-derived action",
            "target": "derive S_cross from Janus bimetric/tetrad/matter sources",
            "success_gate": "deltaS gives E_phi, E_L, K_plus, K_minus and Q_cross from one functional",
        },
        {
            "route": "S_cross candidate triage",
            "target": "restrict future search to source-derived derivative-solder or BF/constraint families",
            "success_gate": "pure pullback, free ultralocal potential and wrong-sign kinetic branches stay rejected",
        },
        {
            "route": "PT/Lie solder action",
            "target": "promote inversion geometry to constraints on phi/L/Omega",
            "success_gate": "constraints follow from group invariance and leave no free observational parameter",
        },
        {
            "route": "Cartan/BF relative connection",
            "target": "derive Phi_R or S_relative, not insert target curvature",
            "success_gate": "F_Omega=Phi_R[source] plus boundary/gauge conditions select L",
        },
        {
            "route": "no-go theorem",
            "target": "prove broad classes of S_cross cannot close without new structure",
            "success_gate": "remaining admissible form is forced or a new axiom is unavoidable",
        },
        {
            "route": "stability/ghost gate",
            "target": "reject actions with wrong-sign kinetic modes, Ostrogradsky terms or unbounded Hamiltonian",
            "success_gate": "linearized spectrum around admissible backgrounds has no ghost branch",
        },
    ]
    required_tooling = [
        "local .venv with numpy/sympy/scipy/matplotlib/pandas/emcee",
        "symbolic EL/Noether checks in sympy",
        "p0_scross_candidate_triage_matrix before proposing any new S_cross",
        "p0_pt_lie_vjanus_ajanus_constraint_solver before treating V_Janus/A_Janus as free",
        "p0_ajanus_branch_selector_dynamics_gate before keeping a PT-like A_Janus branch",
        "p0_ajanus_linear_residual_matching_gate before promoting weak-field selection to covariant closure",
        "p0_ajanus_covariant_lift_obligation before treating a1/a3 as known",
        "p0_covariant_q_field_candidate_gate before reducing Q to a determinant scalar",
        "p0_relative_strain_q_regular_branch_gate before using Q derivatives",
        "p0_relative_strain_dh_lgeom_vs_lorentz_gate before treating Lorentz Omega as strain",
        "p0_sigma_dh_equivalence_gate before introducing Sigma_alpha as a new field",
        "p0_sigma_source_traceability_gap_gate before citing a published Sigma/DH source",
        "p0_sigma_trace_only_no_go_gate before using determinant/B4vol as strain closure",
        "p0_tracefree_h_projector_gate before naming any Q_TF source",
        "p0_tracefree_h_projector_variation_dependency_gate before dropping delta P_STF terms",
        "p0_tracefree_h_source_candidate_matrix before accepting tensor/action Q_TF routes",
        "p0_tracefree_h_irrep_source_requirements_gate before accepting any Q_TF source type",
        "p0_tracefree_h_action_operator_requirements_gate before accepting any Q_TF action operator",
        "p0_tracefree_h_closure_obligation_matrix before promoting Q_TF to prediction input",
        "p0_tracefree_h_scalar_vector_no_go_gate before trying scalar/vector S_TF shortcuts",
        "p0_tracefree_h_variational_source_template_gate before deriving S_TF from action",
        "p0_tracefree_h_variational_action_basis_gate before choosing H/Q action terms",
        "p0_tracefree_h_action_basis_el_variation_gate before using formal EL variations",
        "p0_tracefree_h_action_measure_variation_gate before dropping delta_mu terms",
        "p0_tracefree_h_frechet_log_adjoint_gate before using Q_TF gradients as H gradients",
        "p0_tracefree_h_qtf_to_h_chain_rule_gate before turning Q_TF variations into H equations",
        "p0_tracefree_h_quadratic_qtf_h_el_gate before treating Tr(Q_TF^2) as a source branch",
        "p0_tracefree_h_linear_qtf_xtf_h_el_gate before treating X_TF as a nonzero source branch",
        "p0_same_l_spin_connection_transport_identity_gate before substituting D L residual terms",
        "p0_same_l_bridge_induces_m_k_qcross_gate before treating K/Q_cross/Vlasov bridges as one stack",
        "p0_tracefree_h_janus_coupled_stress_stf_transport_gate before claiming same-bridge X_TF",
        "p0_tracefree_h_xtf_source_provenance_variation_contract before promoting Janus coupled stress STF",
        "p0_tracefree_h_action_basis_acceptance_filter before accepting an action class",
        "p0_tracefree_h_linear_coupling_rank_gate before accepting Q_TF X_TF coupling",
        "p0_tracefree_h_derivative_branch_stability_gate before accepting DQ/DH kinetic branch",
        "p0_tracefree_h_linear_xtf_provenance_gate before accepting Q_TF X_TF source branch",
        "p0_tracefree_h_same_bridge_dependency_gate before accepting Q_TF X_TF variation",
        "p0_tracefree_h_source_action_provenance_chain_gate before accepting S_TF^Janus",
        "p0_tracefree_h_derivation_attack_plan before starting the next S_TF derivation",
        "p0_tracefree_h_anisotropic_stress_gate before replacing H_TF by spatial Pi_TF",
        "p0_tracefree_h_weyl_shear_source_gate before using Weyl/shear diagnostics as source",
        "p0_tracefree_h_vlasov_quadrupole_gate before using kinetic quadrupole closure",
        "p0_tracefree_h_relative_strain_action_gate before accepting relative H/Q action closure",
        "p0_tracefree_h_bf_gl_phi_sigma_gate before accepting BF/GL Phi_Sigma closure",
        "p0_tracefree_h_isotropy_no_go_gate before accepting scalar or FLRW source closure",
        "p0_h_strain_action_variation_gate before accepting V(H) or derivative H action routes",
        "p0_h_strain_ghost_symbolic_gate before accepting derivative H/Q_TF dynamics",
        "p0_nonmetricity_integrability_curl_gate before accepting source N_alpha one-forms",
        "p0_nonmetricity_curl_numeric_probe as diagnostic only, not source proof",
        "p0_nonmetricity_mirror_inverse_gate before treating mirror N_alpha as independent",
        "p0_phi_sigma_source_action_decision_gate before adopting source/action/axiom branch",
        "p0_nonmetricity_source_acceptance_criteria before N/Phi_Sigma becomes prediction input",
        "p0_nonmetricity_rank_reduction_ledger to track remaining trace-free source degrees of freedom",
        "p0_relative_metric_nonmetricity_sigma_dh_gate before using N_alpha=D_alpha H as source",
        "p0_stueckelberg_sigma_dh_variation_rank_gate before claiming Stueckelberg selects strain",
        "p0_cartan_bf_gl_strain_selector_gate before accepting BF/GL strain closure",
        "p0_sigma_source_selector_attack_matrix before claiming a strain source route closes",
        "p0_relative_strain_q_derivative_omega_gate before replacing D log(H) by any shortcut",
        "quadratic ghost/stability gate for candidate actions",
        "bounded numerical PDE/ODE probes in scipy",
        "Lean for small algebraic no-go lemmas",
        "parallel agents split by source extraction, action derivation, no-go, stability",
    ]
    next_agent_tasks = [
        "Agent A: extract PT/Lie/torsor constraints from M31/X2025-symplectic and map to phi/L/Omega",
        "Agent B: derive regular relative strain tensor Q and R_Janus coefficients r1/r3 so a1=r1 and a3=r3",
        "Agent B2: attack relative nonmetricity, Stueckelberg GL/H, and BF/Cartan routes for Sigma_alpha/D_alpha H",
        "Agent C: apply p0_action_ghost_stability_gate to each candidate action",
        "Agent D: no-go expansion for local low-derivative and curvature/BF actions",
    ]
    acceptance_tests = [
        "one same L controls K_plus, K_minus, Q_cross, optics and Vlasov",
        "R_plus=0 and R_minus=0 are forced separately, not only in sum",
        "B_4vol follows from selected J_phi and lapse/slice rule",
        "no hidden fitted scalar, no survey-normalized amplitude, no post-hoc Q absorption",
        "candidate action passes ghost/stability screen before prediction claims",
    ]
    return {
        "description": "Research kernel for a zero-rustine Janus closure search.",
        "status": "infrastructure-ready-physics-open",
        "runtime_ready_target": True,
        "source_action_required": True,
        "free_choice_allowed": False,
        "prediction_ready": False,
        "distinction": distinction,
        "pt_lie_assessment": pt_lie_assessment,
        "closure_routes": closure_routes,
        "required_tooling": required_tooling,
        "next_agent_tasks": next_agent_tasks,
        "acceptance_tests": acceptance_tests,
        "verdict": (
            "PT/Lie geometry is a serious non-rustine route if it becomes a "
            "variational solder principle. As a bare correspondence rule it is only "
            "a geometric ansatz. The closure path is to force S_cross/Phi_R/L from "
            "symmetry plus action plus stability, or prove a no-go."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Non-Rustine Closure Research Kernel",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Runtime ready target: {payload['runtime_ready_target']}",
        f"Source/action required: {payload['source_action_required']}",
        f"Free choice allowed: {payload['free_choice_allowed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Selection Rule",
        "",
        f"Allowed: {payload['distinction']['allowed_selection']}",
        "",
        f"Forbidden: {payload['distinction']['forbidden_choice']}",
        "",
        "## PT/Lie Assessment",
        "",
        "| idea | useful for | not enough for |",
        "|---|---|---|",
    ]
    for row in payload["pt_lie_assessment"]:
        lines.append(f"| {row['idea']} | {row['useful_for']} | {row['not_enough_for']} |")
    lines.extend(["", "## Closure Routes", "", "| route | target | success gate |", "|---|---|---|"])
    for row in payload["closure_routes"]:
        lines.append(f"| {row['route']} | {row['target']} | {row['success_gate']} |")
    lines.extend(["", "## Required Tooling", ""])
    lines.extend(f"- {item}" for item in payload["required_tooling"])
    lines.extend(["", "## Next Agent Tasks", ""])
    lines.extend(f"- {item}" for item in payload["next_agent_tasks"])
    lines.extend(["", "## Acceptance Tests", ""])
    lines.extend(f"- {item}" for item in payload["acceptance_tests"])
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
