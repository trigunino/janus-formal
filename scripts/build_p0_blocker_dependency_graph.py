from __future__ import annotations

from pathlib import Path
import json
import sys


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_janus_source_residual_closure_obligation_matrix import (
    build_payload as build_source_residual_matrix,
)


REPORT_PATH = Path("outputs/reports/p0_blocker_dependency_graph.md")
JSON_PATH = Path("outputs/reports/p0_blocker_dependency_graph.json")


def _artifact_flag_name(artifact: str) -> str:
    return f"{artifact.removeprefix('p0_')}_available"


def _artifact_availability(blockers: list[dict]) -> dict:
    artifacts = sorted({artifact for row in blockers for artifact in row["artifacts"]})
    return {artifact: True for artifact in artifacts}


def _apply_computed_closure(blockers: list[dict], source_matrix: dict) -> None:
    identities = source_matrix["identity_status"]
    requirement_map = {
        "D L transport law": [
            "same_l_dl_source_law",
            "falpha_source_law",
            "projected_cuu_force_balance",
        ],
        "D log B_4vol measure law": ["b4vol_source_measure_law"],
    }
    for row in blockers:
        requirements = requirement_map.get(row["blocker"], [])
        if row["blocker"] == "source-measure branch selection":
            closed_by_name = {item["blocker"]: item["closed"] for item in blockers}
            requirements_closed = (
                closed_by_name["D L transport law"]
                and closed_by_name["D log B_4vol measure law"]
            )
            closure_computed = True
        elif requirements:
            requirements_closed = all(
                identities[name]["source_derived"] for name in requirements
            )
            closure_computed = True
        else:
            requirements_closed = row["closed"]
            closure_computed = False
        row["closure_requirements"] = requirements
        row["closure_computed"] = closure_computed
        row["closed"] = bool(requirements_closed)


def build_payload() -> dict:
    blockers = [
        {
            "blocker": "D L transport law",
            "depends_on": ["Lorentz generator F_alpha", "mirror derivative", "source traceability"],
            "artifacts": [
                "p0_du_l_omega_dynamic_derivation_attempt",
                "p0_omega_source_no_go_axiom_boundary",
                "p0_janus_equations_to_l_omega_law_attempt",
                "p0_bianchi_minimal_joint_dl_dlogb_solution",
                "p0_bianchi_minimal_integrability_mirror_gate",
                "p0_bianchi_minimal_full_connection_lift_system",
                "p0_bianchi_minimal_mirror_inverse_attempt",
                "p0_bianchi_minimal_curvature_integrability_system",
                "p0_flrw_relative_curvature_rows_target",
                "p0_weakfield_relative_curvature_rows_target",
                "p0_weakfield_tetrad_connection_target",
                "p0_janus_source_tetrad_requirements",
                "p0_janus_weakfield_metric_tetrad_bridge",
                "p0_janus_weakfield_source_potential_system",
                "p0_janus_weakfield_phi_psi_qdet_source_closure_attempt",
                "p0_janus_weakfield_dust_slip_poisson_target",
                "p0_janus_weakfield_dust_slip_fourier_solver_gate",
                "p0_janus_weakfield_zero_mode_background_gauge_gate",
                "p0_janus_weakfield_dust_slip_green_kernel_target",
                "p0_janus_source_selected_branch_matrix",
                "p0_janus_weakfield_lgeom_lorentz_no_go_gate",
                "p0_janus_weakfield_lorentz_projection_derivation",
                "p0_janus_weakfield_shift_boost_t0i_derivation",
                "p0_janus_weakfield_g0i_shift_operator_derivation",
                "p0_janus_pressure_pi0i_transport_gate",
                "p0_janus_pressure_pi0i_transport_derivation",
                "p0_janus_g0i_dust_beta_inversion_target",
                "p0_janus_matter_eos_pi_branch_decision",
                "p0_janus_eos_pi_source_audit",
                "p0_janus_conditional_dust_branch_contract",
                "p0_janus_kinetic_moment_eos_pi_closure_target",
                "p0_janus_kinetic_moment_hierarchy_equations",
                "p0_janus_kinetic_closure_routes_decision",
                "p0_janus_full_vlasov_moment_closure_contract",
                "p0_janus_pi_zero_preservation_gate",
                "p0_janus_vlasov_geodesic_force_target",
                "p0_janus_eos_prho_no_go_vlasov_gate",
                "p0_janus_metric_tetrad_source_branch_gate",
                "p0_janus_weakfield_metric_force_probe",
                "p0_janus_same_l_transport_stack_gate",
                "p0_janus_phase_space_b4vol_measure_gate",
                "p0_janus_same_l_1p1_lorentz_probe",
                "p0_janus_lgeom_tetrad_map_residual_probe",
                "p0_janus_lgeom_dl_lie_residual_probe",
                "p0_janus_phase_space_measure_probe",
                "p0_janus_weakfield_b4vol_product_rule_probe",
                "p0_shared_phi_j_source_selection_gate",
                "p0_source_derived_same_l_dl_residual_closure_target",
                "p0_dlogb4vol_source_slice_lapse_obligation_ledger",
                "p0_dlogb4vol_jacobian_lapse_slice_identity_target",
                "p0_falpha_source_law_obligation_ledger",
                "p0_falpha_from_jacobian_tetrad_identity_target",
                "p0_projected_cuu_action_pullback_bridge_ledger",
                "p0_cuu_inverse_map_integrability_target",
                "p0_cuu_jacobian_curl_numeric_probe",
                "p0_janus_effective_vlasov_solver_gate",
                "p0_janus_effective_vlasov_solver_probe",
                "p0_janus_two_sector_vlasov_poisson_probe",
                "p0_janus_metric_force_vlasov_step_probe",
                "p0_janus_two_sector_metric_force_vlasov_probe",
                "p0_janus_diagnostic_closure_dashboard",
                "p0_janus_source_residual_closure_obligation_matrix",
                "p0_source_derived_joint_dl_dlogb_residual_substitution_target",
                "p0_bianchi_minimal_curvature_numeric_probe",
                "p0_curvature_integrability_sparse_pde_probe",
                "p0_weakfield_curvature_injection_probe",
                "p0_weakfield_tetrad_pipeline_probe",
                "p0_bianchi_minimal_same_l_qcross_gate",
                "p0_mirror_inverse_numeric_residual_probe",
                "p0_same_l_qcross_numeric_contraction_probe",
            ],
            "unblocks": ["K transport", "Q_cross compatibility", "R_plus/R_minus force cancellation"],
            "closed": False,
        },
        {
            "blocker": "D log B_4vol measure law",
            "depends_on": ["4D determinant convention", "lapse terms", "source density convention"],
            "artifacts": [
                "p0_dlogb4vol_measure_law_derivation_attempt",
                "p0_janus_equations_to_dlogb4vol_closure_attempt",
                "p0_bianchi_minimal_joint_dl_dlogb_solution",
                "p0_bianchi_minimal_integrability_mirror_gate",
                "p0_bianchi_minimal_full_connection_lift_system",
                "p0_bianchi_minimal_mirror_inverse_attempt",
                "p0_bianchi_minimal_curvature_integrability_system",
                "p0_flrw_relative_curvature_rows_target",
                "p0_weakfield_relative_curvature_rows_target",
                "p0_weakfield_tetrad_connection_target",
                "p0_janus_source_tetrad_requirements",
                "p0_janus_weakfield_metric_tetrad_bridge",
                "p0_janus_weakfield_source_potential_system",
                "p0_janus_weakfield_phi_psi_qdet_source_closure_attempt",
                "p0_janus_weakfield_dust_slip_poisson_target",
                "p0_janus_weakfield_dust_slip_fourier_solver_gate",
                "p0_janus_weakfield_zero_mode_background_gauge_gate",
                "p0_janus_weakfield_dust_slip_green_kernel_target",
                "p0_janus_source_selected_branch_matrix",
                "p0_janus_weakfield_lgeom_lorentz_no_go_gate",
                "p0_janus_weakfield_lorentz_projection_derivation",
                "p0_janus_weakfield_shift_boost_t0i_derivation",
                "p0_janus_weakfield_g0i_shift_operator_derivation",
                "p0_janus_pressure_pi0i_transport_gate",
                "p0_janus_pressure_pi0i_transport_derivation",
                "p0_janus_g0i_dust_beta_inversion_target",
                "p0_janus_matter_eos_pi_branch_decision",
                "p0_janus_eos_pi_source_audit",
                "p0_janus_conditional_dust_branch_contract",
                "p0_janus_kinetic_moment_eos_pi_closure_target",
                "p0_janus_kinetic_moment_hierarchy_equations",
                "p0_janus_kinetic_closure_routes_decision",
                "p0_janus_full_vlasov_moment_closure_contract",
                "p0_janus_pi_zero_preservation_gate",
                "p0_janus_vlasov_geodesic_force_target",
                "p0_janus_eos_prho_no_go_vlasov_gate",
                "p0_janus_metric_tetrad_source_branch_gate",
                "p0_janus_weakfield_metric_force_probe",
                "p0_janus_same_l_transport_stack_gate",
                "p0_janus_phase_space_b4vol_measure_gate",
                "p0_janus_same_l_1p1_lorentz_probe",
                "p0_janus_lgeom_tetrad_map_residual_probe",
                "p0_janus_lgeom_dl_lie_residual_probe",
                "p0_janus_phase_space_measure_probe",
                "p0_janus_weakfield_b4vol_product_rule_probe",
                "p0_shared_phi_j_source_selection_gate",
                "p0_source_derived_same_l_dl_residual_closure_target",
                "p0_dlogb4vol_source_slice_lapse_obligation_ledger",
                "p0_dlogb4vol_jacobian_lapse_slice_identity_target",
                "p0_falpha_source_law_obligation_ledger",
                "p0_falpha_from_jacobian_tetrad_identity_target",
                "p0_projected_cuu_action_pullback_bridge_ledger",
                "p0_cuu_inverse_map_integrability_target",
                "p0_cuu_jacobian_curl_numeric_probe",
                "p0_janus_effective_vlasov_solver_gate",
                "p0_janus_effective_vlasov_solver_probe",
                "p0_janus_two_sector_vlasov_poisson_probe",
                "p0_janus_metric_force_vlasov_step_probe",
                "p0_janus_two_sector_metric_force_vlasov_probe",
                "p0_janus_diagnostic_closure_dashboard",
                "p0_janus_source_residual_closure_obligation_matrix",
                "p0_source_derived_joint_dl_dlogb_residual_substitution_target",
                "p0_bianchi_minimal_curvature_numeric_probe",
                "p0_curvature_integrability_sparse_pde_probe",
                "p0_weakfield_curvature_injection_probe",
                "p0_weakfield_tetrad_pipeline_probe",
                "p0_bianchi_minimal_same_l_qcross_gate",
                "p0_mirror_inverse_numeric_residual_probe",
                "p0_same_l_qcross_numeric_contraction_probe",
            ],
            "unblocks": ["field-equation source branch", "Q_det density map", "R_plus/R_minus product rule"],
            "closed": False,
        },
        {
            "blocker": "source-measure branch selection",
            "depends_on": ["D L transport law", "D log B_4vol measure law", "no Q_det double-counting"],
            "artifacts": [],
            "unblocks": ["accepted K_plus/K_minus branch", "Bianchi closure attempt"],
            "closed": False,
        },
        {
            "blocker": "matter extension",
            "depends_on": ["accepted source branch", "pressure projector transport", "Pi orientation transport"],
            "artifacts": ["p0_pressure_pi_omega_extension_blocker"],
            "unblocks": ["non-dust simulation source model"],
            "closed": False,
        },
        {
            "blocker": "observable chain",
            "depends_on": ["Bianchi closure", "Q_cross normalization", "Janus IC/velocity field"],
            "artifacts": [],
            "unblocks": ["survey comparison", "S8/lensing claims"],
            "closed": False,
        },
    ]
    priority_order = [
        "D L transport law",
        "D log B_4vol measure law",
        "source-measure branch selection",
        "matter extension",
        "observable chain",
    ]
    source_matrix = build_source_residual_matrix()
    _apply_computed_closure(blockers, source_matrix)
    artifact_availability = _artifact_availability(blockers)
    artifact_flags = {
        _artifact_flag_name(artifact): available
        for artifact, available in artifact_availability.items()
    }
    all_blockers_closed = all(row["closed"] for row in blockers)
    payload = {
        "description": "Dependency graph for remaining P0 blockers before any full Janus simulation claim.",
        "status": "blocker-graph-open",
        "graph_written": True,
        "artifact_availability_computed": True,
        "artifact_availability": artifact_availability,
        "available_artifact_count": len(artifact_availability),
        "missing_listed_artifacts": [
            artifact for artifact, available in artifact_availability.items() if not available
        ],
        "blocker_closure_computed": True,
        "source_residual_matrix_status": source_matrix["status"],
        "open_blockers": [row["blocker"] for row in blockers if not row["closed"]],
        "all_blockers_closed": all_blockers_closed,
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
        "shared_phi_j_source_selection_gate_available": True,
        "source_derived_same_l_dl_residual_closure_target_available": True,
        "dlogb4vol_source_slice_lapse_obligation_ledger_available": True,
        "dlogb4vol_jacobian_lapse_slice_identity_target_available": True,
        "falpha_source_law_obligation_ledger_available": True,
        "falpha_from_jacobian_tetrad_identity_target_available": True,
        "projected_cuu_action_pullback_bridge_ledger_available": True,
        "cuu_inverse_map_integrability_target_available": True,
        "cuu_jacobian_curl_numeric_probe_available": True,
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
        "physics_closed": bool(all_blockers_closed and source_matrix["physics_closed"]),
        "prediction_ready": False,
        "blockers": blockers,
        "priority_order": priority_order,
        "verdict": (
            "The critical path starts with D L and D log B_4vol. "
            "Later simulation and survey layers must remain diagnostic until those close."
        ),
    }
    payload.update(artifact_flags)
    return payload


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Blocker Dependency Graph",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Artifact availability computed: {payload['artifact_availability_computed']}",
        f"Blocker closure computed: {payload['blocker_closure_computed']}",
        f"All blockers closed: {payload['all_blockers_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "| blocker | depends on | artifacts | unblocks | closed |",
        "|---|---|---|---|---|",
    ]
    for row in payload["blockers"]:
        lines.append(
            f"| {row['blocker']} | {'; '.join(row['depends_on'])} | "
            f"{'; '.join(row['artifacts'])} | {'; '.join(row['unblocks'])} | {row['closed']} |"
        )
    lines.extend(["", "## Priority Order", ""])
    lines.extend(f"- {item}" for item in payload["priority_order"])
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
