from __future__ import annotations

from pathlib import Path
import json
import sys


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_blocker_dependency_graph import build_payload as build_blocker_graph


REPORT_PATH = Path("outputs/reports/p0_terminal_blockers_status.md")
JSON_PATH = Path("outputs/reports/p0_terminal_blockers_status.json")


def build_payload() -> dict:
    terminal_blockers = [
        {
            "blocker": "d_l_transport_law",
            "owned_by": "p0_blocker_dependency_graph",
            "must_prove": "D L law, same-L K/Q_cross compatibility, and projected Cuu cancellation",
            "closed": False,
        },
        {
            "blocker": "dlogb_4vol_measure_law",
            "owned_by": "p0_blocker_dependency_graph",
            "must_prove": "D log B_4vol law, Q_det convention, and density measure consistency",
            "closed": False,
        },
        {
            "blocker": "source_measure_branch_selection",
            "owned_by": "p0_blocker_dependency_graph",
            "must_prove": "accepted K branch with no Q_det double counting",
            "closed": False,
        },
        {
            "blocker": "matter_extension",
            "owned_by": "p0_blocker_dependency_graph",
            "must_prove": "pressure, Pi, anisotropic stress and non-dust source closure",
            "closed": False,
        },
        {
            "blocker": "observable_chain",
            "owned_by": "p0_blocker_dependency_graph",
            "must_prove": "IC/velocity, Weyl/shear/distance, survey layer and S8/lensing claims",
            "closed": False,
        },
    ]
    graph_payload = build_blocker_graph()
    graph_closed = {row["blocker"]: row["closed"] for row in graph_payload["blockers"]}
    graph_name_by_terminal = {
        "d_l_transport_law": "D L transport law",
        "dlogb_4vol_measure_law": "D log B_4vol measure law",
        "source_measure_branch_selection": "source-measure branch selection",
        "matter_extension": "matter extension",
        "observable_chain": "observable chain",
    }
    for row in terminal_blockers:
        graph_name = graph_name_by_terminal[row["blocker"]]
        row["closed"] = bool(graph_closed[graph_name])
        row["closure_source"] = "p0_blocker_dependency_graph"
    next_best_actions = [
        "inside d_l_transport_law, derive projected Cuu map-force identity from the pulled dust action",
        "use p0_du_l_omega_dynamic_derivation_attempt as the algebraic boundary for D L/Omega",
        "use p0_omega_source_no_go_axiom_boundary to prevent promoting a candidate law to physics",
        "use p0_dlogb4vol_measure_law_derivation_attempt to keep B_4vol distinct from V3_dust",
        "use p0_janus_equations_to_l_omega_law_attempt to record Janus-equation constraints on L/Omega",
        "use p0_janus_equations_to_dlogb4vol_closure_attempt to record source/determinant product-rule limits",
        "use p0_bianchi_minimal_joint_dl_dlogb_solution as the current non-rustine joint branch",
        "use p0_bianchi_minimal_integrability_mirror_gate before promoting the local branch",
        "use p0_bianchi_minimal_full_connection_lift_system to solve transverse boost/rotation equations",
        "use p0_bianchi_minimal_mirror_inverse_attempt to require both residual rows",
        "use p0_bianchi_minimal_curvature_integrability_system to test the source-computable lift PDE",
        "use p0_flrw_relative_curvature_rows_target as the homogeneous source-row target",
        "use p0_weakfield_relative_curvature_rows_target as the restricted perturbative source-row target",
        "use p0_weakfield_tetrad_connection_target to link potentials to spin-connection rows",
        "use p0_janus_source_tetrad_requirements to require source-derived metrics, tetrads, and spin connections",
        "use p0_janus_weakfield_metric_tetrad_bridge to connect Janus weak-field source rows to tetrad probes",
        "use p0_janus_weakfield_source_potential_system to keep Phi/Psi and B_4vol source-derived",
        "use p0_janus_weakfield_phi_psi_qdet_source_closure_attempt to expose determinant feedback without Q_det patching",
        "use p0_janus_weakfield_dust_slip_poisson_target as the conditional coupled dust/slip operator",
        "use p0_janus_weakfield_dust_slip_fourier_solver_gate to expose invertibility and zero-mode blockers",
        "use p0_janus_weakfield_zero_mode_background_gauge_gate to separate source compatibility from common-mode gauge",
        "use p0_janus_weakfield_dust_slip_green_kernel_target as diagnostic mode-handling only",
        "use p0_janus_source_selected_branch_matrix to separate Janus-selected branches from still-open branches",
        "use p0_janus_weakfield_lgeom_lorentz_no_go_gate to reject raw weak-field L_geom as global same-L",
        "use p0_janus_weakfield_lorentz_projection_derivation to derive the scalar weak-field Lorentz part",
        "use p0_janus_weakfield_shift_boost_t0i_derivation to derive the non-comoving shift boost target",
        "use p0_janus_weakfield_g0i_shift_operator_derivation for the linear shift source operator",
        "use p0_janus_pressure_pi0i_transport_gate for non-dust momentum transport",
        "use p0_janus_pressure_pi0i_transport_derivation for same-L pressure/Pi0i algebra",
        "use p0_janus_g0i_dust_beta_inversion_target for the conditional dust beta branch",
        "use p0_janus_matter_eos_pi_branch_decision to keep EOS/Pi source status explicit",
        "use p0_janus_eos_pi_source_audit before promoting any EOS/Pi branch",
        "use p0_janus_conditional_dust_branch_contract for bounded dust diagnostics only",
        "use p0_janus_kinetic_moment_eos_pi_closure_target as the no-fit EOS/Pi route",
        "use p0_janus_kinetic_moment_hierarchy_equations to expose Q_ijk hierarchy blockers",
        "use p0_janus_kinetic_closure_routes_decision before promoting EOS/Pi closure",
        "use p0_janus_full_vlasov_moment_closure_contract to compute Q_ijk from f",
        "use p0_janus_pi_zero_preservation_gate before any Pi=0 promotion",
        "use p0_janus_vlasov_geodesic_force_target to derive A^i_Janus from connection data",
        "use p0_janus_eos_prho_no_go_vlasov_gate to avoid fake scalar EOS closure",
        "use p0_janus_metric_tetrad_source_branch_gate before promoting metric-derived forces",
        "use p0_janus_weakfield_metric_force_probe only as toy Phi/Psi metric-force diagnostic",
        "use p0_janus_same_l_transport_stack_gate before K/Qcross/kinetic projection",
        "use p0_janus_phase_space_b4vol_measure_gate before Vlasov moment normalization",
        "use p0_janus_same_l_1p1_lorentz_probe only as algebraic same-L diagnostic",
        "use p0_janus_lgeom_tetrad_map_residual_probe to keep raw L_geom rejection explicit",
        "use p0_janus_lgeom_dl_lie_residual_probe to keep D L Lie-algebra obstruction explicit",
        "use p0_janus_phase_space_measure_probe only as B4vol/Qdet bookkeeping diagnostic",
        "use p0_janus_weakfield_b4vol_product_rule_probe only as weak-field DlogB diagnostic",
        "use p0_shared_phi_j_source_selection_gate before combining Cuu, Falpha and B4vol",
        "use p0_source_derived_same_l_dl_residual_closure_target as the D L residual acceptance target",
        "use p0_dlogb4vol_source_slice_lapse_obligation_ledger before combining D L and D log B identities",
        "use p0_dlogb4vol_jacobian_lapse_slice_identity_target to separate J_phi, lapse and slice terms",
        "use p0_falpha_source_law_obligation_ledger before promoting any F_alpha branch",
        "use p0_falpha_from_jacobian_tetrad_identity_target to compute D L from integrable J and tetrads",
        "use p0_projected_cuu_action_pullback_bridge_ledger before accepting hE=rho hCuu",
        "use p0_cuu_inverse_map_integrability_target before mirror Cuu closure",
        "use p0_cuu_jacobian_curl_numeric_probe to reject pointwise non-integrable J",
        "use p0_janus_effective_vlasov_solver_gate for diagnostic solver work only",
        "use p0_janus_effective_vlasov_solver_probe only as periodic 1D-1V diagnostic backend",
        "use p0_janus_two_sector_vlasov_poisson_probe only as conjugate-sector diagnostic",
        "use p0_janus_metric_force_vlasov_step_probe only as weak-field metric-force diagnostic",
        "use p0_janus_two_sector_metric_force_vlasov_probe only as combined diagnostic chain",
        "use p0_janus_diagnostic_closure_dashboard as the non-predictive residual rollup",
        "use p0_janus_source_residual_closure_obligation_matrix to bind open source identities to R_plus/R_minus",
        "use p0_source_derived_joint_dl_dlogb_residual_substitution_target to require D L and DlogB4vol together",
        "use p0_bianchi_minimal_curvature_numeric_probe to exercise the scipy closure solver",
        "use p0_curvature_integrability_sparse_pde_probe to detect discrete curl/integrability defects",
        "use p0_weakfield_curvature_injection_probe to inject finite-difference weak-field rows",
        "use p0_weakfield_tetrad_pipeline_probe to check same-L mirror/Q_cross consistency",
        "use p0_bianchi_minimal_same_l_qcross_gate to bind optical contraction to K transport",
        "use p0_mirror_inverse_numeric_residual_probe to test mirrored residual row consistency",
        "use p0_same_l_qcross_numeric_contraction_probe to test geometric same-L optical contractions",
        "use p0_pressure_pi_omega_extension_blocker before any non-dust matter claim",
        "then combine D L and D log B identities into both residual substitutions",
        "only after residual closure, move observable_chain toward physical PM ICs and survey comparison",
    ]
    graph_available_flags = {
        key: value for key, value in graph_payload.items() if key.endswith("_available")
    }
    payload = {
        "description": "Finite terminal blocker status for P0 Janus closure.",
        "status": (
            "terminal-blockers-closed"
            if graph_payload["all_blockers_closed"]
            else "terminal-blockers-open"
        ),
        "terminal_blockers": terminal_blockers,
        "next_best_actions": next_best_actions,
        "finite_blocker_count": len(terminal_blockers),
        "du_l_omega_dynamic_derivation_attempt_available": True,
        "omega_source_no_go_axiom_boundary_available": True,
        "dlogb4vol_measure_law_derivation_attempt_available": True,
        "pressure_pi_omega_extension_blocker_available": True,
        "janus_equations_to_l_omega_law_attempt_available": True,
        "janus_equations_to_dlogb4vol_closure_attempt_available": True,
        "bianchi_minimal_joint_dl_dlogb_solution_available": True,
        "bianchi_minimal_integrability_mirror_gate_available": True,
        "bianchi_minimal_full_connection_lift_system_available": True,
        "bianchi_minimal_mirror_inverse_attempt_available": True,
        "bianchi_minimal_curvature_integrability_system_available": True,
        "flrw_relative_curvature_rows_target_available": True,
        "weakfield_relative_curvature_rows_target_available": True,
        "weakfield_tetrad_connection_target_available": True,
        "janus_source_tetrad_requirements_available": True,
        "janus_weakfield_metric_tetrad_bridge_available": True,
        "janus_weakfield_source_potential_system_available": True,
        "janus_weakfield_phi_psi_qdet_source_closure_attempt_available": True,
        "janus_weakfield_dust_slip_poisson_target_available": True,
        "janus_weakfield_dust_slip_fourier_solver_gate_available": True,
        "janus_weakfield_zero_mode_background_gauge_gate_available": True,
        "janus_weakfield_dust_slip_green_kernel_target_available": True,
        "janus_source_selected_branch_matrix_available": True,
        "janus_weakfield_lgeom_lorentz_no_go_gate_available": True,
        "janus_weakfield_lorentz_projection_derivation_available": True,
        "janus_weakfield_shift_boost_t0i_derivation_available": True,
        "janus_weakfield_g0i_shift_operator_derivation_available": True,
        "janus_pressure_pi0i_transport_gate_available": True,
        "janus_pressure_pi0i_transport_derivation_available": True,
        "janus_g0i_dust_beta_inversion_target_available": True,
        "janus_matter_eos_pi_branch_decision_available": True,
        "janus_eos_pi_source_audit_available": True,
        "janus_conditional_dust_branch_contract_available": True,
        "janus_kinetic_moment_eos_pi_closure_target_available": True,
        "janus_kinetic_moment_hierarchy_equations_available": True,
        "janus_kinetic_closure_routes_decision_available": True,
        "janus_full_vlasov_moment_closure_contract_available": True,
        "janus_pi_zero_preservation_gate_available": True,
        "janus_vlasov_geodesic_force_target_available": True,
        "janus_eos_prho_no_go_vlasov_gate_available": True,
        "janus_metric_tetrad_source_branch_gate_available": True,
        "janus_weakfield_metric_force_probe_available": True,
        "janus_same_l_transport_stack_gate_available": True,
        "janus_phase_space_b4vol_measure_gate_available": True,
        "janus_same_l_1p1_lorentz_probe_available": True,
        "janus_lgeom_tetrad_map_residual_probe_available": True,
        "janus_lgeom_dl_lie_residual_probe_available": True,
        "janus_phase_space_measure_probe_available": True,
        "janus_weakfield_b4vol_product_rule_probe_available": True,
        "source_derived_same_l_dl_residual_closure_target_available": True,
        "dlogb4vol_source_slice_lapse_obligation_ledger_available": True,
        "falpha_source_law_obligation_ledger_available": True,
        "projected_cuu_action_pullback_bridge_ledger_available": True,
        "janus_effective_vlasov_solver_gate_available": True,
        "janus_effective_vlasov_solver_probe_available": True,
        "janus_two_sector_vlasov_poisson_probe_available": True,
        "janus_metric_force_vlasov_step_probe_available": True,
        "janus_two_sector_metric_force_vlasov_probe_available": True,
        "janus_diagnostic_closure_dashboard_available": True,
        "janus_source_residual_closure_obligation_matrix_available": True,
        "bianchi_minimal_curvature_numeric_probe_available": True,
        "curvature_integrability_sparse_pde_probe_available": True,
        "weakfield_curvature_injection_probe_available": True,
        "weakfield_tetrad_pipeline_probe_available": True,
        "bianchi_minimal_same_l_qcross_gate_available": True,
        "mirror_inverse_numeric_residual_probe_available": True,
        "same_l_qcross_numeric_contraction_probe_available": True,
        "blocker_graph_consumed": True,
        "open_terminal_blockers": [
            row["blocker"] for row in terminal_blockers if not row["closed"]
        ],
        "all_terminal_blockers_closed": bool(graph_payload["all_blockers_closed"]),
        "physics_closed": bool(graph_payload["physics_closed"]),
        "prediction_ready": bool(graph_payload["prediction_ready"]),
        "verdict": (
            "The work is bounded: current open work reduces to these terminal blockers. "
            "The next proof pass is ledger-driven: close same-L/DL, DlogB4vol, Falpha, "
            "and Cuu source obligations before R_plus/R_minus substitution."
        ),
    }
    payload.update(graph_available_flags)
    return payload


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Terminal Blockers Status",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Finite blocker count: {payload['finite_blocker_count']}",
        f"Blocker graph consumed: {payload['blocker_graph_consumed']}",
        "D_u L/Omega dynamic derivation attempt available: "
        f"{payload['du_l_omega_dynamic_derivation_attempt_available']}",
        "Omega source no-go axiom boundary available: "
        f"{payload['omega_source_no_go_axiom_boundary_available']}",
        "D log B4vol measure-law derivation attempt available: "
        f"{payload['dlogb4vol_measure_law_derivation_attempt_available']}",
        "Pressure/Pi Omega extension blocker available: "
        f"{payload['pressure_pi_omega_extension_blocker_available']}",
        "Janus equations to L/Omega law attempt available: "
        f"{payload['janus_equations_to_l_omega_law_attempt_available']}",
        "Janus equations to DlogB4vol closure attempt available: "
        f"{payload['janus_equations_to_dlogb4vol_closure_attempt_available']}",
        "Bianchi-minimal joint DL/DlogB solution available: "
        f"{payload['bianchi_minimal_joint_dl_dlogb_solution_available']}",
        "Bianchi-minimal integrability/mirror gate available: "
        f"{payload['bianchi_minimal_integrability_mirror_gate_available']}",
        "Bianchi-minimal full connection lift system available: "
        f"{payload['bianchi_minimal_full_connection_lift_system_available']}",
        "Bianchi-minimal mirror inverse attempt available: "
        f"{payload['bianchi_minimal_mirror_inverse_attempt_available']}",
        "Bianchi-minimal curvature integrability system available: "
        f"{payload['bianchi_minimal_curvature_integrability_system_available']}",
        "FLRW relative curvature rows target available: "
        f"{payload['flrw_relative_curvature_rows_target_available']}",
        "Weak-field relative curvature rows target available: "
        f"{payload['weakfield_relative_curvature_rows_target_available']}",
        "Weak-field tetrad connection target available: "
        f"{payload['weakfield_tetrad_connection_target_available']}",
        "Janus source tetrad requirements available: "
        f"{payload['janus_source_tetrad_requirements_available']}",
        "Janus weak-field metric/tetrad bridge available: "
        f"{payload['janus_weakfield_metric_tetrad_bridge_available']}",
        "Janus weak-field source potential system available: "
        f"{payload['janus_weakfield_source_potential_system_available']}",
        "Janus weak-field Phi/Psi/Qdet closure attempt available: "
        f"{payload['janus_weakfield_phi_psi_qdet_source_closure_attempt_available']}",
        "Janus weak-field dust/slip Poisson target available: "
        f"{payload['janus_weakfield_dust_slip_poisson_target_available']}",
        "Janus weak-field dust/slip Fourier solver gate available: "
        f"{payload['janus_weakfield_dust_slip_fourier_solver_gate_available']}",
        "Janus weak-field zero-mode background gauge gate available: "
        f"{payload['janus_weakfield_zero_mode_background_gauge_gate_available']}",
        "Janus weak-field dust/slip Green kernel target available: "
        f"{payload['janus_weakfield_dust_slip_green_kernel_target_available']}",
        "Janus source-selected branch matrix available: "
        f"{payload['janus_source_selected_branch_matrix_available']}",
        "Janus weak-field Lgeom Lorentz no-go gate available: "
        f"{payload['janus_weakfield_lgeom_lorentz_no_go_gate_available']}",
        "Janus weak-field Lorentz projection derivation available: "
        f"{payload['janus_weakfield_lorentz_projection_derivation_available']}",
        "Janus weak-field shift boost T0i derivation available: "
        f"{payload['janus_weakfield_shift_boost_t0i_derivation_available']}",
        "Janus weak-field G0i shift operator derivation available: "
        f"{payload['janus_weakfield_g0i_shift_operator_derivation_available']}",
        "Janus pressure/Pi0i transport gate available: "
        f"{payload['janus_pressure_pi0i_transport_gate_available']}",
        "Janus pressure/Pi0i transport derivation available: "
        f"{payload['janus_pressure_pi0i_transport_derivation_available']}",
        "Janus G0i dust beta inversion target available: "
        f"{payload['janus_g0i_dust_beta_inversion_target_available']}",
        "Janus matter EOS/Pi branch decision available: "
        f"{payload['janus_matter_eos_pi_branch_decision_available']}",
        "Janus EOS/Pi source audit available: "
        f"{payload['janus_eos_pi_source_audit_available']}",
        "Janus conditional dust branch contract available: "
        f"{payload['janus_conditional_dust_branch_contract_available']}",
        "Janus kinetic moment EOS/Pi closure target available: "
        f"{payload['janus_kinetic_moment_eos_pi_closure_target_available']}",
        "Janus kinetic moment hierarchy equations available: "
        f"{payload['janus_kinetic_moment_hierarchy_equations_available']}",
        "Janus kinetic closure routes decision available: "
        f"{payload['janus_kinetic_closure_routes_decision_available']}",
        "Janus full Vlasov moment closure contract available: "
        f"{payload['janus_full_vlasov_moment_closure_contract_available']}",
        "Janus Pi zero preservation gate available: "
        f"{payload['janus_pi_zero_preservation_gate_available']}",
        "Janus Vlasov geodesic force target available: "
        f"{payload['janus_vlasov_geodesic_force_target_available']}",
        "Janus EOS p(rho) no-go Vlasov gate available: "
        f"{payload['janus_eos_prho_no_go_vlasov_gate_available']}",
        "Janus metric/tetrad source branch gate available: "
        f"{payload['janus_metric_tetrad_source_branch_gate_available']}",
        "Janus weak-field metric force probe available: "
        f"{payload['janus_weakfield_metric_force_probe_available']}",
        "Janus same-L transport stack gate available: "
        f"{payload['janus_same_l_transport_stack_gate_available']}",
        "Janus phase-space B4vol measure gate available: "
        f"{payload['janus_phase_space_b4vol_measure_gate_available']}",
        "Janus same-L 1+1 Lorentz probe available: "
        f"{payload['janus_same_l_1p1_lorentz_probe_available']}",
        "Janus Lgeom tetrad map residual probe available: "
        f"{payload['janus_lgeom_tetrad_map_residual_probe_available']}",
        "Janus Lgeom DL Lie residual probe available: "
        f"{payload['janus_lgeom_dl_lie_residual_probe_available']}",
        "Janus phase-space measure probe available: "
        f"{payload['janus_phase_space_measure_probe_available']}",
        "Janus weak-field B4vol product-rule probe available: "
        f"{payload['janus_weakfield_b4vol_product_rule_probe_available']}",
        "Janus effective Vlasov solver gate available: "
        f"{payload['janus_effective_vlasov_solver_gate_available']}",
        "Janus effective Vlasov solver probe available: "
        f"{payload['janus_effective_vlasov_solver_probe_available']}",
        "Janus two-sector Vlasov-Poisson probe available: "
        f"{payload['janus_two_sector_vlasov_poisson_probe_available']}",
        "Janus metric-force Vlasov step probe available: "
        f"{payload['janus_metric_force_vlasov_step_probe_available']}",
        "Janus two-sector metric-force Vlasov probe available: "
        f"{payload['janus_two_sector_metric_force_vlasov_probe_available']}",
        "Bianchi-minimal curvature numeric probe available: "
        f"{payload['bianchi_minimal_curvature_numeric_probe_available']}",
        "Curvature integrability sparse PDE probe available: "
        f"{payload['curvature_integrability_sparse_pde_probe_available']}",
        "Weak-field curvature injection probe available: "
        f"{payload['weakfield_curvature_injection_probe_available']}",
        "Weak-field tetrad pipeline probe available: "
        f"{payload['weakfield_tetrad_pipeline_probe_available']}",
        "Bianchi-minimal same-L Q_cross gate available: "
        f"{payload['bianchi_minimal_same_l_qcross_gate_available']}",
        "Mirror inverse numeric residual probe available: "
        f"{payload['mirror_inverse_numeric_residual_probe_available']}",
        "Same-L Q_cross numeric contraction probe available: "
        f"{payload['same_l_qcross_numeric_contraction_probe_available']}",
        f"All terminal blockers closed: {payload['all_terminal_blockers_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "| blocker | owned by | must prove | closed |",
        "|---|---|---|---|",
    ]
    for row in payload["terminal_blockers"]:
        lines.append(
            f"| {row['blocker']} | `{row['owned_by']}` | {row['must_prove']} | {row['closed']} |"
        )
    lines.extend(["", "## Next Best Actions", ""])
    lines.extend(f"- {item}" for item in payload["next_best_actions"])
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
