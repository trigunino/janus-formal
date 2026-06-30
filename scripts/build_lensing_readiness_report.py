from __future__ import annotations

from pathlib import Path
import json

try:
    from scripts.build_survey_likelihood_interface_report import build_payload as build_survey_payload
except ModuleNotFoundError:
    from build_survey_likelihood_interface_report import build_payload as build_survey_payload


QDET_PATH = Path("outputs/reports/lensing_qdet_convention_audit.json")
QCROSS_PATH = Path("outputs/reports/lensing_qcross_audit.json")
PREFACTOR_PATH = Path("outputs/reports/lensing_prefactor_audit.json")
QDET_TARGET_PATH = Path("outputs/reports/qdet_metric_volume_target.json")
QDET_DENSITY_MEASURE_TARGET_PATH = Path("outputs/reports/qdet_density_measure_target.json")
QCROSS_TARGET_PATH = Path("outputs/reports/qcross_four_velocity_target.json")
QCROSS_COVARIANT_TARGET_PATH = Path(
    "outputs/reports/qcross_covariant_projection_target.json"
)
QCROSS_TETRAD_MAP_TARGET_PATH = Path("outputs/reports/qcross_tetrad_map_target.json")
QCROSS_FLRW_COMOVING_TETRAD_BRANCH_PATH = Path(
    "outputs/reports/qcross_flrw_comoving_tetrad_branch.json"
)
QCROSS_GEOMETRIC_TETRAD_MAP_DERIVATION_PATH = Path(
    "outputs/reports/qcross_geometric_tetrad_map_derivation.json"
)
QCROSS_NONCOMOVING_BOOST_BRANCH_PATH = Path(
    "outputs/reports/qcross_noncomoving_boost_branch.json"
)
COUPLED_FIELD_PATH = Path("outputs/reports/coupled_field_equations_audit.json")
BIANCHI_CLOSURE_PATH = Path("outputs/reports/bianchi_closure_target.json")
BIANCHI_RESIDUAL_TARGET_PATH = Path(
    "outputs/reports/bianchi_mixed_stress_residual_target.json"
)
BIANCHI_ANSATZ_AUDIT_PATH = Path("outputs/reports/bianchi_ansatz_audit.json")
BIANCHI_MIXED_TRANSPORT_MAP_TARGET_PATH = Path(
    "outputs/reports/bianchi_mixed_transport_map_target.json"
)
BIANCHI_FLRW_DUST_TRANSPORT_BRANCH_PATH = Path(
    "outputs/reports/bianchi_flrw_dust_transport_branch.json"
)
BIANCHI_FLRW_LAPSE_VOLUME_AUDIT_PATH = Path(
    "outputs/reports/bianchi_flrw_lapse_volume_audit.json"
)
BIANCHI_FLRW_PERFECT_FLUID_TRANSPORT_BRANCH_PATH = Path(
    "outputs/reports/bianchi_flrw_perfect_fluid_transport_branch.json"
)
BIANCHI_ANISOTROPIC_STRESS_TRANSPORT_TARGET_PATH = Path(
    "outputs/reports/bianchi_anisotropic_stress_transport_target.json"
)
INTERACTION_TENSOR_ATTEMPT_PATH = Path(
    "outputs/reports/interaction_tensor_attempt_audit.json"
)
PM_QCROSS_PATH = Path("outputs/reports/pm_state_qcross.json")
PM_QCROSS_SOURCE_PATH = Path("outputs/reports/pm_qcross_lensing_source.json")
PM_QCROSS_PIPELINE_PATH = Path("outputs/reports/pm_qcross_lensing_pipeline.json")
PM_QCROSS_ABSOLUTE_SHEAR_PATH = Path("outputs/reports/pm_qcross_absolute_shear.json")
PM_BAND_LIMITED_SHEAR_CONVERGENCE_PATH = Path(
    "outputs/reports/pm_band_limited_shear_convergence.json"
)
PM_TIME_LENSING_CALIBRATION_PATH = Path(
    "outputs/reports/pm_time_lensing_normalization_calibration.json"
)
SCAFFOLDS_AUDIT_PATH = Path("outputs/reports/temporary_scaffolds_audit.json")
JANUS_LINEAR_IC_TARGET_PATH = Path("outputs/reports/janus_linear_ic_equations_target.json")
JANUS_LINEAR_GROWTH_MODES_PATH = Path("outputs/reports/janus_linear_growth_modes.json")
JANUS_LINEAR_GROWTH_PROPAGATOR_PATH = Path(
    "outputs/reports/janus_linear_growth_propagator.json"
)
JANUS_LINEAR_IC_BACKGROUND_OPERATOR_PATH = Path(
    "outputs/reports/janus_linear_ic_background_operator_target.json"
)
SURVEY_LIKELIHOOD_INTERFACE_PATH = Path("outputs/reports/survey_likelihood_interface.json")
SURVEY_DATA_CONTRACT_PATH = Path("outputs/reports/survey_data_contract.json")
PM_RELATIVISTIC_STABILITY_PATH = Path(
    "outputs/reports/pm_relativistic_velocity_stability.json"
)
OBSERVABLE_CHAIN_CONSISTENCY_PATH = Path(
    "outputs/reports/observable_chain_consistency_audit.json"
)
METRIC_POTENTIAL_PROMOTION_GATE_PATH = Path(
    "outputs/reports/p0_stueckelberg_metric_potential_promotion_gate.json"
)
RESTRICTED_METRIC_WEYL_CHAIN_PATH = Path("outputs/reports/restricted_metric_weyl_chain.json")
BETA_FIELD_PROVENANCE_GATE_PATH = Path(
    "outputs/reports/p0_stueckelberg_beta_field_provenance_gate.json"
)
REPORT_PATH = Path("outputs/reports/lensing_readiness_report.md")
JSON_PATH = Path("outputs/reports/lensing_readiness_report.json")


def load_json(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def main() -> None:
    qdet = load_json(QDET_PATH)
    qcross = load_json(QCROSS_PATH)
    prefactor = load_json(PREFACTOR_PATH)
    metric_potential = load_json(METRIC_POTENTIAL_PROMOTION_GATE_PATH)
    restricted_weyl = load_json(RESTRICTED_METRIC_WEYL_CHAIN_PATH)
    beta_gate = load_json(BETA_FIELD_PROVENANCE_GATE_PATH)
    survey = build_survey_payload()
    missing_survey_inputs = ", ".join(survey["missing_survey_inputs"])

    gates = [
        {
            "gate": "Q_det convention",
            "status": "partial",
            "current": "newtonian_effective_density is admissible as weak-field convention",
            "blocks_s8": True,
            "next_required": "derive metric-volume mapping for tensor lensing",
        },
        {
            "gate": "Q_cross projection",
            "status": "partial",
            "current": "Q_cross=1 is derived for aligned comoving FLRW tetrads; PM velocity/source diagnostics remain local conventions",
            "blocks_s8": True,
            "next_required": "derive perturbed/global L_minus_to_plus beyond the aligned FLRW branch",
        },
        {
            "gate": "Beta field provenance",
            "status": "diagnostic only",
            "current": "PM/H0 beta fields are usable diagnostics; source-derived Janus beta is unavailable",
            "blocks_s8": True,
            "next_required": "derive beta_vec from Janus transfer/growth/velocity dynamics",
        },
        {
            "gate": "absolute prefactor",
            "status": "partial",
            "current": "H0^-1 PM time calibration and factorized C_J normalization are implemented",
            "blocks_s8": True,
            "next_required": "prove or reject non-unity tensor factors before survey likelihood",
        },
        {
            "gate": "Bianchi closure",
            "status": "open",
            "current": "weak-field branches are admissible diagnostics; exact mixed stress tensors are not closed",
            "blocks_s8": True,
            "next_required": "derive D_plus.S_plus=0 and D_minus.S_minus=0 for the coupled RHS",
        },
        {
            "gate": "Metric potential / Weyl",
            "status": "restricted partial",
            "current": "Poisson potential is promotable only for the comoving scalar zero-Pi branch",
            "blocks_s8": True,
            "next_required": "derive non-comoving, pressure/Pi and full tensor metric-potential closure",
        },
        {
            "gate": "S8_eff",
            "status": "not admissible",
            "current": f"survey layer absent; missing {missing_survey_inputs}",
            "blocks_s8": True,
            "next_required": "supply n(z), tomographic bins, observed vector, covariance and mask/window",
        },
    ]
    payload = {
        "description": "Readiness status before any Janus weak-lensing S8_eff claim.",
        "verdict": "Not ready for S8_eff. Current work is a controlled diagnostic, not a final prediction.",
        "source_reports": {
            "qdet": str(QDET_PATH),
            "qcross": str(QCROSS_PATH),
            "prefactor": str(PREFACTOR_PATH),
            "qdet_metric_volume_target": str(QDET_TARGET_PATH),
            "qdet_density_measure_target": str(QDET_DENSITY_MEASURE_TARGET_PATH),
            "qcross_four_velocity_target": str(QCROSS_TARGET_PATH),
            "qcross_covariant_projection_target": str(QCROSS_COVARIANT_TARGET_PATH),
            "qcross_tetrad_map_target": str(QCROSS_TETRAD_MAP_TARGET_PATH),
            "qcross_flrw_comoving_tetrad_branch": str(
                QCROSS_FLRW_COMOVING_TETRAD_BRANCH_PATH
            ),
            "qcross_geometric_tetrad_map_derivation": str(
                QCROSS_GEOMETRIC_TETRAD_MAP_DERIVATION_PATH
            ),
            "qcross_noncomoving_boost_branch": str(
                QCROSS_NONCOMOVING_BOOST_BRANCH_PATH
            ),
            "coupled_field_equations": str(COUPLED_FIELD_PATH),
            "bianchi_closure": str(BIANCHI_CLOSURE_PATH),
            "bianchi_mixed_stress_residual_target": str(BIANCHI_RESIDUAL_TARGET_PATH),
            "bianchi_ansatz_audit": str(BIANCHI_ANSATZ_AUDIT_PATH),
            "bianchi_mixed_transport_map_target": str(
                BIANCHI_MIXED_TRANSPORT_MAP_TARGET_PATH
            ),
            "bianchi_flrw_dust_transport_branch": str(
                BIANCHI_FLRW_DUST_TRANSPORT_BRANCH_PATH
            ),
            "bianchi_flrw_lapse_volume_audit": str(
                BIANCHI_FLRW_LAPSE_VOLUME_AUDIT_PATH
            ),
            "bianchi_flrw_perfect_fluid_transport_branch": str(
                BIANCHI_FLRW_PERFECT_FLUID_TRANSPORT_BRANCH_PATH
            ),
            "bianchi_anisotropic_stress_transport_target": str(
                BIANCHI_ANISOTROPIC_STRESS_TRANSPORT_TARGET_PATH
            ),
            "interaction_tensor_attempt": str(INTERACTION_TENSOR_ATTEMPT_PATH),
            "pm_qcross": str(PM_QCROSS_PATH),
            "pm_qcross_source": str(PM_QCROSS_SOURCE_PATH),
            "pm_qcross_pipeline": str(PM_QCROSS_PIPELINE_PATH),
            "pm_qcross_absolute_shear": str(PM_QCROSS_ABSOLUTE_SHEAR_PATH),
            "pm_band_limited_shear_convergence": str(
                PM_BAND_LIMITED_SHEAR_CONVERGENCE_PATH
            ),
            "pm_time_lensing_calibration": str(PM_TIME_LENSING_CALIBRATION_PATH),
            "temporary_scaffolds": str(SCAFFOLDS_AUDIT_PATH),
            "janus_linear_ic_equations_target": str(JANUS_LINEAR_IC_TARGET_PATH),
            "janus_linear_growth_modes": str(JANUS_LINEAR_GROWTH_MODES_PATH),
            "janus_linear_growth_propagator": str(JANUS_LINEAR_GROWTH_PROPAGATOR_PATH),
            "janus_linear_ic_background_operator_target": str(
                JANUS_LINEAR_IC_BACKGROUND_OPERATOR_PATH
            ),
            "survey_likelihood_interface": str(SURVEY_LIKELIHOOD_INTERFACE_PATH),
            "survey_data_contract": str(SURVEY_DATA_CONTRACT_PATH),
            "pm_relativistic_velocity_stability": str(PM_RELATIVISTIC_STABILITY_PATH),
            "observable_chain_consistency": str(OBSERVABLE_CHAIN_CONSISTENCY_PATH),
            "metric_potential_promotion_gate": str(METRIC_POTENTIAL_PROMOTION_GATE_PATH),
            "restricted_metric_weyl_chain": str(RESTRICTED_METRIC_WEYL_CHAIN_PATH),
            "beta_field_provenance_gate": str(BETA_FIELD_PROVENANCE_GATE_PATH),
        },
        "source_verdicts": {
            "qdet": qdet["verdict"],
            "qcross": qcross["verdict"],
            "prefactor": prefactor["verdict"],
        },
        "survey_layer": {
            "ready": survey["survey_layer_ready"],
            "missing_inputs": survey["missing_survey_inputs"],
            "can_call_outputs_predictions": survey["can_call_outputs_predictions"],
        },
        "metric_potential_layer": {
            "restricted_metric_ready": metric_potential["decision"][
                "poisson_potential_promotable_for_restricted_comoving_scalar_branch"
            ],
            "general_metric_ready": metric_potential["decision"][
                "poisson_potential_promotable_to_metric_potential"
            ],
            "restricted_numeric_rows": len(restricted_weyl["rows"]),
            "restricted_numeric_prediction_ready": restricted_weyl["prediction_ready"],
        },
        "beta_field_layer": {
            "pm_calibrated_beta_usable_as_diagnostic": beta_gate["decision"][
                "pm_calibrated_beta_usable_as_diagnostic"
            ],
            "source_derived_beta_available": beta_gate["decision"][
                "source_derived_beta_available"
            ],
            "prediction_ready": beta_gate["decision"]["prediction_ready"],
        },
        "gates": gates,
    }
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")

    lines = [
        "# Lensing Readiness Report",
        "",
        payload["description"],
        "",
        "| gate | status | current | blocks S8_eff | next required |",
        "|---|---|---|---|---|",
    ]
    for row in gates:
        lines.append(
            f"| {row['gate']} | {row['status']} | {row['current']} | "
            f"{row['blocks_s8']} | {row['next_required']} |"
        )
    lines.extend(
        [
            "",
            "## Source Verdicts",
            "",
            f"- Q_det: {qdet['verdict']}",
            f"- Q_cross: {qcross['verdict']}",
            f"- Prefactor: {prefactor['verdict']}",
            f"- Survey layer ready: {survey['survey_layer_ready']}",
            f"- Missing survey inputs: {missing_survey_inputs}",
            "",
            f"Verdict: {payload['verdict']}",
            "",
        ]
    )
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {JSON_PATH}")


if __name__ == "__main__":
    main()
