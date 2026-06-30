from __future__ import annotations

from pathlib import Path
import json
import sys


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_nonmetricity_integrability_curl_gate import (
    build_payload as build_integrability,
)
from scripts.build_p0_nonmetricity_mirror_inverse_gate import (
    build_payload as build_mirror,
)
from scripts.build_p0_relative_metric_nonmetricity_sigma_dh_gate import (
    build_payload as build_nonmetricity,
)
from scripts.build_p0_sigma_source_traceability_gap_gate import (
    build_payload as build_traceability,
)
from scripts.build_p0_sigma_trace_only_no_go_gate import (
    build_payload as build_trace_no_go,
)
from scripts.build_p0_tracefree_h_isotropy_no_go_gate import (
    build_payload as build_isotropy_no_go,
)
from scripts.build_p0_tracefree_h_projector_gate import (
    build_payload as build_tracefree_projector,
)
from scripts.build_p0_tracefree_h_source_candidate_matrix import (
    build_payload as build_source_candidates,
)
from scripts.build_p0_same_l_bridge_induces_m_k_qcross_gate import (
    build_payload as build_same_l_bridge_stack,
)


REPORT_PATH = Path("outputs/reports/p0_nonmetricity_source_acceptance_criteria.md")
JSON_PATH = Path("outputs/reports/p0_nonmetricity_source_acceptance_criteria.json")


def build_payload() -> dict:
    traceability = build_traceability()
    nonmetricity = build_nonmetricity()
    trace_no_go = build_trace_no_go()
    tracefree_projector = build_tracefree_projector()
    source_candidates = build_source_candidates()
    isotropy_no_go = build_isotropy_no_go()
    integrability = build_integrability()
    mirror = build_mirror()
    same_l_bridge_stack = build_same_l_bridge_stack()
    criteria = [
        {
            "criterion": "published_or_action_source",
            "requires": "explicit N_alpha/Phi_Sigma/D_alpha H/Sigma_alpha equation before residual substitution",
            "passed": bool(traceability["published_sigma_dh_source_found"]),
        },
        {
            "criterion": "definition_not_selector",
            "requires": "N_alpha=D_alpha H is treated as a definition, not a source law",
            "passed": bool(nonmetricity["n_definition_closed"] and not nonmetricity["source_selector_found"]),
        },
        {
            "criterion": "trace_free_channel",
            "requires": "source selects trace-free Q_TF/Sigma_TF, not only determinant trace",
            "passed": False,
        },
        {
            "criterion": "tracefree_projector_defined",
            "requires": "P_TF isolates the 9-component H_TF/Q_TF target before source selection",
            "passed": bool(tracefree_projector["projector_defined"]),
        },
        {
            "criterion": "tracefree_source_candidates_bounded",
            "requires": "candidate tensor/action source routes are enumerated and remain unaccepted without Janus source/action",
            "passed": bool(not source_candidates["any_candidate_accepted"]),
        },
        {
            "criterion": "isotropy_no_go_applied",
            "requires": "density, pressure, determinant and FLRW scalar closures are rejected for Q_TF",
            "passed": bool(isotropy_no_go["isotropic_sources_have_zero_tf_projection"]),
        },
        {
            "criterion": "trace_only_no_go_applied",
            "requires": "determinant/B4vol trace-only closure rejected",
            "passed": bool(trace_no_go["no_go_closed"]),
        },
        {
            "criterion": "curl_integrability",
            "requires": "source N integrates to one same H with correct covariant curl",
            "passed": bool(integrability["source_n_integrability_proved"]),
        },
        {
            "criterion": "mirror_inverse",
            "requires": "mirror branch uses H^{-1} and induced N_mirror, not independent source",
            "passed": bool(mirror["mirror_identity_closed"] and not mirror["independent_mirror_n_allowed"]),
        },
        {
            "criterion": "same_l_qcross_vlasov",
            "requires": "same L/Gamma branch feeds K, Q_cross, optics and Vlasov, then Janus source-selects it",
            "passed": bool(
                same_l_bridge_stack["same_l_stack_algebra_closed"]
                and same_l_bridge_stack["l_source_selected"]
            ),
        },
        {
            "criterion": "ghost_stability",
            "requires": "any derivative H/GL strain action passes ghost/tachyon screen",
            "passed": False,
        },
    ]
    return {
        "description": "Acceptance criteria before N_alpha/Phi_Sigma may become a Janus prediction input.",
        "status": "nonmetricity-source-acceptance-open",
        "depends_on": [
            "p0_phi_sigma_source_action_decision_gate",
            "p0_sigma_source_traceability_gap_gate",
            "p0_relative_metric_nonmetricity_sigma_dh_gate",
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
            "p0_nonmetricity_integrability_curl_gate",
            "p0_nonmetricity_mirror_inverse_gate",
            "p0_nonmetricity_rank_reduction_ledger",
            "p0_h_strain_ghost_symbolic_gate",
        ],
        "criteria": criteria,
        "criteria_passed": sum(1 for row in criteria if row["passed"]),
        "criteria_total": len(criteria),
        "accepted_as_prediction_input": False,
        "source_selection_closed": False,
        "prediction_ready": False,
        "no_rustine_rules": [
            "no residual-cancel target N_alpha",
            "no observational fit for Phi_Sigma or Q_TF amplitude",
            "no determinant trace promoted to tensor strain",
            "no independent mirror N source",
        ],
        "verdict": (
            "N_alpha/Phi_Sigma is not accepted as a prediction input. Algebraic "
            "definition, trace-only no-go and mirror identity are useful progress; "
            "source traceability, trace-free selection, curl integrability, same-L "
            "transport and ghost stability remain open."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Nonmetricity Source Acceptance Criteria",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Criteria passed: {payload['criteria_passed']}/{payload['criteria_total']}",
        f"Accepted as prediction input: {payload['accepted_as_prediction_input']}",
        f"Source selection closed: {payload['source_selection_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Criteria",
        "",
        "| criterion | requires | passed |",
        "|---|---|---:|",
    ]
    for row in payload["criteria"]:
        lines.append(f"| {row['criterion']} | {row['requires']} | {row['passed']} |")
    lines.extend(["", "## Depends On", ""])
    lines.extend(f"- `{item}`" for item in payload["depends_on"])
    lines.extend(["", "## No-Rustine Rules", ""])
    lines.extend(f"- {item}" for item in payload["no_rustine_rules"])
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
