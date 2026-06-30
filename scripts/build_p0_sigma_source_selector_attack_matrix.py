from __future__ import annotations

from pathlib import Path
import json
import sys


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_sigma_dh_equivalence_gate import build_payload as build_sigma_gate


REPORT_PATH = Path("outputs/reports/p0_sigma_source_selector_attack_matrix.md")
JSON_PATH = Path("outputs/reports/p0_sigma_source_selector_attack_matrix.json")


def build_payload() -> dict:
    sigma_gate = build_sigma_gate()
    routes = [
        {
            "route": "published_janus_lgeom_source_equation",
            "zero_rustine": True,
            "selects_sigma_dh": False,
            "verdict": "target route; no explicit source-selected Gamma/Sigma law is recorded here yet",
        },
        {
            "route": "relative_metric_nonmetricity",
            "zero_rustine": True,
            "selects_sigma_dh": "conditional",
            "verdict": "viable only if Janus derives N_alpha=D_alpha H as a source equation",
        },
        {
            "route": "stueckelberg_two_diffeo_action",
            "zero_rustine": True,
            "selects_sigma_dh": False,
            "verdict": "current Lorentz-only L variation has zero direct rank on Sigma/DH; needs GL/H extension",
        },
        {
            "route": "stueckelberg_gl_h_extension",
            "zero_rustine": True,
            "selects_sigma_dh": "conditional",
            "verdict": "possible only if source action varies raw L_geom or H and passes overconstraint/ghost gates",
        },
        {
            "route": "cartan_bf_gl_strain_connection",
            "zero_rustine": True,
            "selects_sigma_dh": "conditional",
            "verdict": "viable only if BF curvature/source and ghost gate fix the symmetric GL strain sector",
        },
        {
            "route": "h_strain_derivative_action",
            "zero_rustine": True,
            "selects_sigma_dh": "conditional",
            "verdict": "ultralocal V(H) is insufficient; derivative H dynamics can work only if source-derived and ghost-stable",
        },
        {
            "route": "matter_vlasov_anisotropic_stress",
            "zero_rustine": True,
            "selects_sigma_dh": "partial",
            "verdict": "can constrain projections/orientation, not full Sigma without kinetic source closure",
        },
        {
            "route": "pure_lorentz_omega",
            "zero_rustine": True,
            "selects_sigma_dh": False,
            "verdict": "rejected as nontrivial strain source because eta-antisymmetric Omega gives D H=0",
        },
        {
            "route": "determinant_b4vol_trace_only",
            "zero_rustine": True,
            "selects_sigma_dh": False,
            "verdict": "reject as sole selector: it controls only Tr(Q), not trace-free strain",
        },
        {
            "route": "observational_residual_cancellation",
            "zero_rustine": False,
            "selects_sigma_dh": False,
            "verdict": "forbidden fit/rustine",
        },
    ]
    accepted = [
        row for row in routes if row["selects_sigma_dh"] is True
    ]
    conditional = [
        row for row in routes if row["selects_sigma_dh"] in ("conditional", "partial")
    ]
    return {
        "description": "Attack matrix for zero-rustine source selection of the Sigma_alpha/D_alpha H strain channel.",
        "status": "sigma-source-selector-open",
        "depends_on": [
            "p0_sigma_source_traceability_gap_gate",
            "p0_sigma_dh_equivalence_gate",
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
            "p0_relative_metric_nonmetricity_sigma_dh_gate",
            "p0_stueckelberg_sigma_dh_variation_rank_gate",
            "p0_cartan_bf_gl_strain_selector_gate",
        ],
        "sigma_dh_equivalence_closed": sigma_gate["identity_closed"],
        "routes": routes,
        "routes_attacked": len(routes),
        "routes_selecting_sigma_dh": len(accepted),
        "conditional_routes": [row["route"] for row in conditional],
        "forbidden_routes": [
            row["route"] for row in routes if row["zero_rustine"] is False
        ],
        "required_closure_tests": [
            "upgrade p0_sigma_source_traceability_gap_gate before citing a published source",
            "apply p0_sigma_trace_only_no_go_gate before using determinant/B4vol as strain closure",
            "apply p0_tracefree_h_projector_gate before naming any Q_TF source",
            "apply p0_tracefree_h_projector_variation_dependency_gate before dropping delta P_STF terms",
            "apply p0_tracefree_h_source_candidate_matrix before accepting tensor/action routes",
            "apply Q_TF irrep and action-operator requirement gates before claiming source selection",
            "apply p0_tracefree_h_closure_obligation_matrix before promoting Q_TF to prediction input",
            "apply scalar/vector no-go and variational source template before deriving S_TF^Janus",
            "apply variational action basis, linear coupling rank and derivation attack plan before accepting an action branch",
            "apply action-basis EL variation and acceptance filter before promoting formal variations",
            "apply action-measure variation gate before dropping delta_mu terms",
            "apply FrechetLog adjoint gate before using Q_TF gradients as H gradients",
            "apply Q_TF-to-H chain rule before replacing Q_TF variations by H equations",
            "apply quadratic Q_TF H-EL gate before using Tr(Q_TF^2) as anything beyond formal algebra",
            "apply linear Q_TF X_TF H-EL gate before using X_TF as a nonzero source",
            "apply same-L spin-connection identity gate before substituting D L residual terms",
            "apply same-L bridge induction gate before treating K/Q_cross/Vlasov bridges as one stack",
            "apply Janus coupled-stress STF transport gate before claiming same-bridge X_TF",
            "apply X_TF source provenance variation contract before promoting Janus coupled stress STF",
            "apply derivative branch stability and linear X_TF provenance gates before following best next branches",
            "apply same-bridge dependency and source-action provenance chain gates before accepting S_TF^Janus",
            "apply Pi_TF, Weyl/shear and Vlasov Q_TF subgates before promoting tensor diagnostics",
            "apply relative-strain-action and BF/GL Phi_Sigma Q_TF subgates before promoting action routes",
            "apply p0_tracefree_h_isotropy_no_go_gate before accepting scalar or FLRW source closure",
            "apply p0_h_strain_action_variation_gate before accepting V(H) or (D H)^2 action routes",
            "apply p0_h_strain_ghost_symbolic_gate before accepting derivative H/Q_TF dynamics",
            "apply p0_nonmetricity_integrability_curl_gate before accepting N_alpha source one-forms",
            "use p0_nonmetricity_curl_numeric_probe as diagnostic only, not proof",
            "apply p0_nonmetricity_mirror_inverse_gate before treating mirror N as independent",
            "apply p0_phi_sigma_source_action_decision_gate before adopting source/action/axiom branch",
            "derive Gamma_alpha/Sigma_alpha from Janus source/action before residual substitution",
            "prove trace-free Q_TF is selected, not only determinant/B4vol trace",
            "prove mirror inverse plus/minus branch for the same strain channel",
            "prove same L induces K_plus, K_minus, Q_cross and Vlasov transport",
            "pass ghost/stability gate if the route introduces GL/symmetric strain dynamics",
        ],
        "source_selection_closed": False,
        "prediction_ready": False,
        "verdict": (
            "No route currently selects Sigma_alpha/D_alpha H. The best non-rustine "
            "branches are relative nonmetricity, Stueckelberg GL/H extension, or Cartan/BF "
            "symmetric strain, but each remains conditional."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Sigma Source Selector Attack Matrix",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Sigma/DH equivalence closed: {payload['sigma_dh_equivalence_closed']}",
        f"Routes attacked: {payload['routes_attacked']}",
        f"Routes selecting Sigma/DH: {payload['routes_selecting_sigma_dh']}",
        f"Source selection closed: {payload['source_selection_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Routes",
        "",
        "| route | zero rustine | selects Sigma/DH | verdict |",
        "|---|---:|---:|---|",
    ]
    for row in payload["routes"]:
        lines.append(
            f"| {row['route']} | {row['zero_rustine']} | "
            f"{row['selects_sigma_dh']} | {row['verdict']} |"
        )
    lines.extend(["", "## Conditional Routes", ""])
    lines.extend(f"- `{item}`" for item in payload["conditional_routes"])
    lines.extend(["", "## Forbidden Routes", ""])
    lines.extend(f"- `{item}`" for item in payload["forbidden_routes"])
    lines.extend(["", "## Required Closure Tests", ""])
    lines.extend(f"- {item}" for item in payload["required_closure_tests"])
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
