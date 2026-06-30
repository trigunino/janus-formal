from __future__ import annotations

from pathlib import Path
import json
import sys


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

REPORT_PATH = Path("outputs/reports/p0_next_session_handoff.md")
JSON_PATH = Path("outputs/reports/p0_next_session_handoff.json")


def load_upstream_status() -> tuple[dict, dict, str | None]:
    try:
        from scripts.build_p0_terminal_blockers_status import (
            build_payload as build_terminal_blockers,
        )
        from scripts.build_p0_zero_rustine_phi_j_l_route_attack_matrix import (
            build_payload as build_zero_rustine_matrix,
        )

        return build_zero_rustine_matrix(), build_terminal_blockers(), None
    except ModuleNotFoundError as exc:
        matrix = {
            "routes_attacked": 13,
            "routes_selecting_phi_j_l": 0,
        }
        terminal = {"status": "dependency-unavailable"}
        return matrix, terminal, str(exc)


def build_payload() -> dict:
    matrix, terminal, dependency_fallback = load_upstream_status()
    proven = [
        "B4vol fixes a product, not J_phi",
        "single diagonal Noether identity is rank 1",
        "phase-space Liouville preservation does not select spacetime J_phi",
        "Lorentz/tetrad admissibility leaves rapidity and D L free",
        "pure matter pullback is an identity, not a map selector",
        "projected dust force shape rho h Cuu is conditional progress",
        "higher-derivative D L terms produce PDEs but need source data",
        "curvature couplings produce equations but need source data",
        "nonlocal kernels can hide a target unless kernel/target are source-derived",
        "restricted easy local S_couple class is eliminated",
    ]
    open_verrous = [
        {
            "name": "source_derived_phi_j_l_selector",
            "why_open": "13 zero-rustine routes attacked, none selects general phi/J/L",
            "next": "derive source action/identity or prove broader no-go",
        },
        {
            "name": "split_noether_or_two_sector_identity",
            "why_open": "rank-one diagonal identity cannot force both R_plus and R_minus",
            "next": "derive independent sector identity or source-derived split equation",
        },
        {
            "name": "same_l_dl_rapidity_transport",
            "why_open": "Lorentz admissibility is necessary but not selective",
            "next": "derive source rapidity/DL law tied to K, Q_cross and kinetic projection",
        },
        {
            "name": "b4vol_lapse_slice_selector",
            "why_open": "B4vol=J_phi*S_slice has compensating gauge freedom",
            "next": "derive lapse/slice/gauge selector from Janus branch",
        },
        {
            "name": "matter_eos_pi_vlasov",
            "why_open": "dust branch is conditional; pressure/Pi need EOS, Pi law or Vlasov moments",
            "next": "keep kinetic/Vlasov as no-fit matter route",
        },
        {
            "name": "tracefree_h_qtf_source",
            "why_open": "projector and scalar no-go are defined, but no Janus source/action selects Q_TF",
            "next": "derive anisotropic stress, Weyl/shear, Vlasov quadrupole, strain action or BF/GL source",
        },
        {
            "name": "residual_substitution",
            "why_open": "R_plus=R_minus=0 not proven with same phi/L/B4vol",
            "next": "substitute only after source selector and matter law exist",
        },
    ]
    next_actions = [
        {
            "priority": "P0",
            "action": "Use non-rustine closure kernel to coordinate PT/Lie, action, BF and no-go branches",
            "success": "all candidate selections are forced by source/action/symmetry/stability or rejected",
        },
        {
            "priority": "P0",
            "action": "Use S_cross triage before inventing new couplings",
            "success": "only source-derived derivative-solder or BF/constraint families remain under investigation",
        },
        {
            "priority": "P0",
            "action": "Use PT/Lie parity constraints before treating V_Janus or A_Janus as free",
            "success": "forbidden polynomial branches are removed before any fit or source comparison",
        },
        {
            "priority": "P0",
            "action": "Check whether Janus source requires nondegenerate linear A_Janus transport",
            "success": "weak-field linear residual matching rejects PT-like branch; next promote to full covariant closure",
        },
        {
            "priority": "P0",
            "action": "Promote A_Janus matching to covariant q/Q and R_Janus coefficients",
            "success": "a1=r1 and a3=r3 with r1/r3 source-derived, not fitted",
        },
        {
            "priority": "P0",
            "action": "Use relative strain tensor Q instead of determinant scalar q",
            "success": "same-L anisotropic solder data is retained in the A_Janus lift",
        },
        {
            "priority": "P0",
            "action": "Use Q=1/2 log(H) only on a regular polar/log branch",
            "success": "mirror Q->-Q and trace/determinant separation are explicit",
        },
        {
            "priority": "P0",
            "action": "Use Q_TF-to-H chain rule before accepting H equations from Q_TF variations",
            "success": "FrechetLog_H, projector dependencies, same bridge and commuting-branch limits are explicit",
        },
        {
            "priority": "P0",
            "action": "Use FrechetLog adjoint gate before treating Q_TF gradients as H gradients",
            "success": "off-diagonal divided-difference kernel and adjoint pairing are explicit",
        },
        {
            "priority": "P0",
            "action": "Use quadratic Q_TF H-EL gate before accepting Tr(Q_TF^2)",
            "success": "formal H-gradient is separated from Janus source provenance",
        },
        {
            "priority": "P0",
            "action": "Use linear Q_TF X_TF H-EL gate before accepting a nonzero source",
            "success": "X_TF provenance, same bridge and dependency terms are closed before prediction",
        },
        {
            "priority": "P0",
            "action": "Attack X_TF source contract through Janus coupled stress STF first",
            "success": "P_STF(T_self+B4vol T_other_to_self) is transported on the same bridge or rejected",
        },
        {
            "priority": "P0",
            "action": "Use coupled-stress STF transport gate algebra before bridge closure",
            "success": "4D STF rank-2 type is coherent and scalar absorption stays forbidden",
        },
        {
            "priority": "P0",
            "action": "Separate raw L_geom strain from pure Lorentz Omega before using Q",
            "success": "D_alpha H depends on eta-symmetric Sigma_alpha; pure Lorentz Omega gives D_alpha H=0",
        },
        {
            "priority": "P0",
            "action": "Treat Sigma_alpha and D_alpha H as one source-selection problem",
            "success": "no double counting: Sigma_alpha is not an independent knob beyond D_alpha H",
        },
        {
            "priority": "P0",
            "action": "Attack Sigma/DH source selection through nonmetricity, Stueckelberg and BF branches",
            "success": "one branch derives the strain channel, or each branch becomes a bounded no-go",
        },
        {
            "priority": "P0",
            "action": "Use Sigma/DH source traceability before citing recent Janus papers as closure",
            "success": "published-source claim requires explicit N_alpha, Phi_Sigma, D_alpha H or Sigma_alpha equation",
        },
        {
            "priority": "P0",
            "action": "Apply trace-only no-go before using B4vol/Q_det as strain closure",
            "success": "determinant trace is kept separate from trace-free Sigma/Q_TF",
        },
        {
            "priority": "P0",
            "action": "Use trace-free H projector and source candidate matrix before any Q_TF claim",
            "success": "scalar/FLRW closures stay rejected and tensor/action candidates require Janus source/action",
        },
        {
            "priority": "P0",
            "action": "Use projector-variation dependency gate before dropping delta P_STF",
            "success": "fixed-projector, covariant-H and screen-congruence branches are separated",
        },
        {
            "priority": "P0",
            "action": "Use action-measure variation gate before dropping delta_mu",
            "success": "fixed measure, metric volume, B4vol and absorbed-measure branches are separated",
        },
        {
            "priority": "P0",
            "action": "Use H-strain action gate before accepting V(H) or (D H)^2 routes",
            "success": "ultralocal potentials are not mistaken for D_alpha H selectors; derivative actions remain source/ghost gated",
        },
        {
            "priority": "P0",
            "action": "Apply nonmetricity curl gate before accepting any source N_alpha",
            "success": "N_alpha integrates to one same H and mirror H^{-1}; curl defects are rejected",
        },
        {
            "priority": "P0",
            "action": "Apply mirror inverse gate before treating minus-sector N as independent",
            "success": "N_mirror is induced by H^{-1}; only the original N branch remains source-open",
        },
        {
            "priority": "P0",
            "action": "Use Phi_Sigma decision and N acceptance gates before promoting any branch",
            "success": "source/action/new-axiom path is explicit and N/Phi_Sigma is not a prediction input prematurely",
        },
        {
            "priority": "P0",
            "action": "Use numerical curl probe only as diagnostic support",
            "success": "compatible dH closes and injected curl defects fail, without claiming source proof",
        },
        {
            "priority": "P0",
            "action": "Use rank ledger to focus on the remaining trace-free H source branch",
            "success": "work targets the 9 trace-free H components after trace and mirror reductions",
        },
        {
            "priority": "P0",
            "action": "Use nonmetricity, Stueckelberg rank and BF/GL gates before any Sigma/DH closure claim",
            "success": "relative N_alpha, GL/H Stueckelberg and BF/Cartan branches are separately accepted or rejected",
        },
        {
            "priority": "P0",
            "action": "Use the Q derivative gate before any D log(H) manipulation",
            "success": "DQ is FrechetLog_H[D_alpha H] from same Omega_alpha; no scalar shortcut unless commuting branch is proved",
        },
        {
            "priority": "P0",
            "action": "Try source-derived Stueckelberg/two-diffeomorphism action",
            "success": "deltaS gives phi/L equations and independent split Noether identities",
        },
        {
            "priority": "P0",
            "action": "Extend restricted no-go toward full local low-derivative class",
            "success": "DL, curvature, matter, B4vol and Noether obstructions are unified in one theorem",
        },
        {
            "priority": "P0",
            "action": "Attack Cartan/BF relative-connection route",
            "success": "source relative curvature fixes Omega/L without path or holonomy fit",
        },
        {
            "priority": "P1",
            "action": "Formalize small algebraic obstructions in Lean",
            "success": "rank-one Noether and B4vol product degeneracy become machine-checked lemmas",
        },
        {
            "priority": "P1",
            "action": "Keep Vlasov/moment route ready for matter extension",
            "success": "pressure/Pi are computed from f, not scalar absorbed",
        },
    ]
    parallel_agents = [
        "Agent A: Stueckelberg/two-diffeomorphism source-action derivation",
        "Agent B: no-go theorem expansion for local low-derivative S_couple",
        "Agent C: Cartan/BF relative connection and curvature integrability",
        "Agent D: kinetic/Vlasov EOS-Pi route, diagnostic only until same-L exists",
    ]
    guardrails = [
        "no observational fit or post-hoc normalization",
        "no Q_det/Q_cross scalar absorption",
        "no hidden new axiom; label any new principle explicitly",
        "do not promote FLRW/comoving conditional branch to general perturbations",
        "do not claim prediction_ready before R_plus=R_minus=0",
    ]
    key_artifacts = [
        "p0_non_rustine_closure_research_kernel",
        "p0_scross_candidate_triage_matrix",
        "p0_pt_lie_vjanus_ajanus_constraint_solver",
        "p0_ajanus_branch_selector_dynamics_gate",
        "p0_ajanus_linear_residual_matching_gate",
        "p0_ajanus_covariant_lift_obligation",
        "p0_covariant_q_field_candidate_gate",
        "p0_relative_strain_q_regular_branch_gate",
        "p0_relative_strain_dh_lgeom_vs_lorentz_gate",
        "p0_sigma_dh_equivalence_gate",
        "p0_sigma_source_traceability_gap_gate",
        "p0_sigma_trace_only_no_go_gate",
        "p0_tracefree_h_projector_gate",
        "p0_tracefree_h_projector_variation_dependency_gate",
        "p0_tracefree_h_source_candidate_matrix",
        "p0_tracefree_h_irrep_source_requirements_gate",
        "p0_tracefree_h_action_operator_requirements_gate",
        "p0_tracefree_h_closure_obligation_matrix",
        "p0_tracefree_h_scalar_vector_no_go_gate",
        "p0_tracefree_h_variational_source_template_gate",
        "p0_tracefree_h_variational_action_basis_gate",
        "p0_tracefree_h_action_basis_el_variation_gate",
        "p0_tracefree_h_action_measure_variation_gate",
        "p0_tracefree_h_frechet_log_adjoint_gate",
        "p0_tracefree_h_qtf_to_h_chain_rule_gate",
        "p0_tracefree_h_quadratic_qtf_h_el_gate",
        "p0_tracefree_h_linear_qtf_xtf_h_el_gate",
        "p0_same_l_spin_connection_transport_identity_gate",
        "p0_same_l_bridge_induces_m_k_qcross_gate",
        "p0_tracefree_h_janus_coupled_stress_stf_transport_gate",
        "p0_tracefree_h_xtf_source_provenance_variation_contract",
        "p0_tracefree_h_action_basis_acceptance_filter",
        "p0_tracefree_h_linear_coupling_rank_gate",
        "p0_tracefree_h_derivative_branch_stability_gate",
        "p0_tracefree_h_linear_xtf_provenance_gate",
        "p0_tracefree_h_same_bridge_dependency_gate",
        "p0_tracefree_h_source_action_provenance_chain_gate",
        "p0_tracefree_h_derivation_attack_plan",
        "p0_tracefree_h_anisotropic_stress_gate",
        "p0_tracefree_h_weyl_shear_source_gate",
        "p0_tracefree_h_vlasov_quadrupole_gate",
        "p0_tracefree_h_relative_strain_action_gate",
        "p0_tracefree_h_bf_gl_phi_sigma_gate",
        "p0_tracefree_h_isotropy_no_go_gate",
        "p0_h_strain_action_variation_gate",
        "p0_h_strain_ghost_symbolic_gate",
        "p0_nonmetricity_integrability_curl_gate",
        "p0_nonmetricity_curl_numeric_probe",
        "p0_nonmetricity_mirror_inverse_gate",
        "p0_phi_sigma_source_action_decision_gate",
        "p0_nonmetricity_source_acceptance_criteria",
        "p0_nonmetricity_rank_reduction_ledger",
        "p0_relative_metric_nonmetricity_sigma_dh_gate",
        "p0_stueckelberg_sigma_dh_variation_rank_gate",
        "p0_cartan_bf_gl_strain_selector_gate",
        "p0_sigma_source_selector_attack_matrix",
        "p0_relative_strain_q_derivative_omega_gate",
        "p0_action_ghost_stability_gate",
        "p0_minimal_janus_soldering_principle_candidate",
        "p0_zero_rustine_phi_j_l_route_attack_matrix",
        "p0_bf_connection_constraint_route",
        "p0_stueckelberg_two_diffeo_route",
        "p0_phi_j_l_remaining_lock_decision_matrix",
        "p0_matter_pullback_action_deep_audit",
        "p0_local_low_derivative_scouple_restricted_no_go",
        "p0_noether_split_rank_obstruction",
        "p0_b4vol_jacobian_gauge_degeneracy_proof",
        "p0_terminal_blockers_status",
    ]
    return {
        "description": "Next-session handoff for P0 Janus zero-rustine closure work.",
        "status": "handoff-ready-physics-open",
        "routes_attacked": matrix["routes_attacked"],
        "routes_selecting_phi_j_l": matrix["routes_selecting_phi_j_l"],
        "prediction_ready": False,
        "terminal_blockers_closed": terminal["status"] == "terminal-blockers-closed",
        "dependency_fallback": dependency_fallback,
        "proven_or_stabilized": proven,
        "open_verrous": open_verrous,
        "next_actions": next_actions,
        "parallel_agents": parallel_agents,
        "guardrails": guardrails,
        "key_artifacts": key_artifacts,
        "recommended_start": (
            "Start from p0_non_rustine_closure_research_kernel, then compare "
            "minimal soldering, BF relative connection, source-derived Stueckelberg action, "
            "ghost/stability gates, and no-go theorem expansion."
        ),
        "verdict": (
            "The workspace is cleanly organized around one fact: no zero-rustine route "
            "currently selects general phi/J/L. Next session should either derive a real "
            "Janus source identity/action or convert more candidate families into bounded no-go results."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Next Session Handoff",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Routes attacked: {payload['routes_attacked']}",
        f"Routes selecting phi/J/L: {payload['routes_selecting_phi_j_l']}",
        f"Terminal blockers closed: {payload['terminal_blockers_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        f"Dependency fallback: {payload['dependency_fallback']}",
        "",
        "## Proven Or Stabilized",
        "",
    ]
    lines.extend(f"- {item}" for item in payload["proven_or_stabilized"])
    lines.extend(
        [
            "",
            "## Open Verrous",
            "",
            "| name | why open | next |",
            "|---|---|---|",
        ]
    )
    for row in payload["open_verrous"]:
        lines.append(f"| {row['name']} | {row['why_open']} | {row['next']} |")
    lines.extend(
        [
            "",
            "## Next Actions",
            "",
            "| priority | action | success |",
            "|---|---|---|",
        ]
    )
    for row in payload["next_actions"]:
        lines.append(f"| {row['priority']} | {row['action']} | {row['success']} |")
    lines.extend(["", "## Parallel Agents", ""])
    lines.extend(f"- {item}" for item in payload["parallel_agents"])
    lines.extend(["", "## Guardrails", ""])
    lines.extend(f"- {item}" for item in payload["guardrails"])
    lines.extend(["", "## Key Artifacts", ""])
    lines.extend(f"- `{item}`" for item in payload["key_artifacts"])
    lines.extend(["", f"Recommended start: {payload['recommended_start']}", ""])
    lines.extend([f"Verdict: {payload['verdict']}", ""])
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
