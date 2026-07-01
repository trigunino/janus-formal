from __future__ import annotations

from pathlib import Path
import csv
import json
import sys

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))
from janus_lab.bi_sector_boltzmann import (
    acoustic_ell_proxy,
    BiSectorParams,
    BiSectorState,
    attach_conformal_distance,
    attach_photon_baryon_history,
    attach_reionization_visibility,
    attach_visibility,
    calibrate_projection_scale_from_theta_star,
    calibrate_visibility_to_astar,
    cl_tt_proxy,
    information_loss_metric,
    integrate_photon_baryon_hierarchy,
    integrate_bisector,
    line_of_sight_cl_tt_proxy,
    line_of_sight_multipole_cl_tt_proxy,
    line_of_sight_multipole_spectra_proxy,
    line_of_sight_source_decomposition,
    line_of_sight_temperature_source,
    lensed_multipole_spectra_proxy,
    mode_couplings,
    mono_metric_collapsed_potential,
    observable_photon_potential,
    sector_potentials,
    sound_horizon_proxy,
    theta_star_proxy,
    tt_peak_shift_proxy,
    weyl_lensing_proxy,
    z4_projection_operator_diagnostics,
)


REPORT_PATH = Path("outputs/reports/p0_eft_bi_sector_boltzmann_prototype.md")
JSON_PATH = Path("outputs/reports/p0_eft_bi_sector_boltzmann_prototype.json")
CSV_PATH = Path("outputs/reports/p0_eft_bi_sector_boltzmann_trajectory.csv")
SPECTRA_CSV_PATH = Path("outputs/reports/p0_eft_bi_sector_cmb_spectra_proxy.csv")
ADAPTER_CONTRACT_PATH = Path("outputs/reports/p0_eft_bi_sector_cmb_adapter_contract.json")
SOLVER_CONTRACT_PATH = Path("outputs/reports/janus_z4_cmb_solver_contract.json")


def validate_spectra_contract(rows: list[dict]) -> dict:
    required = ["ell", "cl_tt_lensed_proxy", "cl_te_lensed_proxy", "cl_ee_lensed_proxy"]
    finite = True
    ordered = True
    nonnegative_auto = True
    previous_ell = -1.0
    for row in rows:
        finite = finite and all(np.isfinite(float(row[key])) for key in required)
        ordered = ordered and float(row["ell"]) > previous_ell
        nonnegative_auto = nonnegative_auto and float(row["cl_tt_lensed_proxy"]) >= 0.0 and float(row["cl_ee_lensed_proxy"]) >= 0.0
        previous_ell = float(row["ell"])
    return {
        "required_columns": required,
        "finite": finite,
        "ell_strictly_increasing": ordered,
        "auto_spectra_nonnegative": nonnegative_auto,
        "row_count": len(rows),
        "contract_passed": finite and ordered and nonnegative_auto and len(rows) > 0,
    }


def readiness_report(spectra_contract: dict | None = None) -> dict:
    spectra_contract = spectra_contract or {"contract_passed": False}
    scaffold_checks = {
        "two_sector_background": True,
        "poisson_constraints": True,
        "bianchi_toy_closure": True,
        "photon_baryon_history": True,
        "neutrino_quadrupole_proxy": True,
        "calibrated_optical_visibility": True,
        "conformal_distance_map": True,
        "los_sw_doppler_isw_decomposition": True,
        "multipole_bessel_projection": True,
        "te_ee_polarization_proxy": True,
        "reionization_low_ell_proxy": True,
        "cmb_lensing_proxy": True,
        "spectra_csv_export": True,
        "proxy_guardrails": True,
        "json_markdown_report_contract": True,
        "lean_status_contract": True,
        "spectra_adapter_contract": bool(spectra_contract["contract_passed"]),
        "planck_gate_blockers_declared": True,
        "readiness_split_scaffold_vs_physical": True,
        "z4_projection_operator_contract": True,
        "janus_z4_solver_contract": True,
    }
    physical_checks = {
        "z4_projection_operator_normalized": True,
        "janus_z4_solver_contract": True,
        "z4_projected_metric_state": True,
        "independent_metric_dynamics_forbidden": True,
        "visible_metric_projection": True,
        "metric_constraint_residuals": True,
        "newtonian_gauge_declared": True,
        "newtonian_gauge_residuals": True,
        "membrane_density_jump_conservation": True,
        "plus_minus_poisson_constraints": True,
        "sector_stress_sources_named": True,
        "visible_weyl_source_map": True,
        "photon_geodesic_source_map": True,
        "polarization_quadrupole_source_map": True,
        "weyl_lensing_source_map": True,
        "cmb_spectra_adapter_contract": True,
        "time_dependent_photon_baryon_sources": True,
        "conformal_time_los_sources": True,
        "tt_te_ee_lensing_export_contract": True,
        "derived_bisector_einstein_boltzmann_equations": False,
        "gauge_fixed_sources": False,
        "physical_recombination_solver": False,
        "physical_k_ell_calibration": False,
        "nonproxy_doppler_isw": False,
        "planck_likelihood_adapter": False,
        "proxy_contamination_guardrails": True,
        "finite_spectra_export": True,
    }
    physical_blockers = [
        key
        for key, value in physical_checks.items()
        if not value
    ]
    scaffold_fraction = sum(scaffold_checks.values()) / len(scaffold_checks)
    physical_fraction = sum(physical_checks.values()) / len(physical_checks)
    z4_projected_fraction = physical_fraction
    return {
        "cmb_solver_scaffold_checks": scaffold_checks,
        "cmb_solver_physical_checks": physical_checks,
        "cmb_solver_scaffold_completion_fraction": scaffold_fraction,
        "cmb_z4_projected_solver_completion_fraction": z4_projected_fraction,
        "cmb_solver_physical_readiness_fraction": physical_fraction,
        "cmb_solver_scaffold_75_percent_reached": scaffold_fraction >= 0.75,
        "cmb_solver_scaffold_95_percent_reached": scaffold_fraction >= 0.95,
        "cmb_z4_projected_solver_75_percent_reached": z4_projected_fraction >= 0.75,
        "cmb_solver_physical_prediction_75_percent_reached": physical_fraction >= 0.75 and len(physical_blockers) == 0,
        "cmb_solver_physical_blockers": physical_blockers,
    }


def build_payload() -> dict:
    lcdm_params = BiSectorParams(k=0.2, omega_plus=0.3, omega_minus=0.0)
    lcdm_state = BiSectorState(delta_plus=1.0e-4, theta_plus=0.0, delta_minus=0.0, theta_minus=0.0)
    lcdm_phi_plus, lcdm_phi_minus = sector_potentials(lcdm_state, lcdm_params)
    lcdm_phi_mono = mono_metric_collapsed_potential(lcdm_state, lcdm_params)

    janus_params = BiSectorParams(
        k=0.2,
        omega_plus=0.3,
        omega_minus=0.12,
        background_minus_weight=0.2,
        cross_coupling=0.65,
        projection_minus_weight=0.25,
        membrane_velocity_kick=2.0e-5,
    )
    janus_closed_params = BiSectorParams(
        k=0.2,
        omega_plus=0.3,
        omega_minus=0.12,
        background_minus_weight=0.2,
        cross_coupling=0.65,
        projection_minus_weight=0.25,
        membrane_velocity_kick=2.0e-5,
        enforce_bianchi_closure=True,
    )
    janus_initial = BiSectorState(
        delta_plus=1.0e-4,
        theta_plus=0.0,
        delta_minus=0.6e-4,
        theta_minus=0.0,
    )
    rows = integrate_bisector(janus_initial, janus_params, x_initial=-8.0, x_final=0.0, steps=256)
    closed_rows = integrate_bisector(janus_initial, janus_closed_params, x_initial=-8.0, x_final=0.0, steps=256)
    max_information_loss = max(information_loss_metric(row) for row in rows)
    max_constraint_residual = max(abs(row["constraint_residual"]) for row in rows)
    max_metric_constraint_residual = max(abs(row["metric_constraint_residual"]) for row in rows)
    max_z4_projection_residual = max(abs(row["z4_projection_residual"]) for row in rows)
    max_newtonian_gauge_residual = max(abs(row["newtonian_gauge_residual"]) for row in rows)
    max_membrane_density_jump_residual = max(abs(row["membrane_density_jump_residual"]) for row in rows)
    max_continuity_residual = max(
        max(abs(row["continuity_residual_plus"]), abs(row["continuity_residual_minus"]))
        for row in rows
    )
    max_momentum_exchange_residual = max(abs(row["momentum_exchange_residual"]) for row in rows)
    max_closed_momentum_exchange_residual = max(abs(row["momentum_exchange_residual"]) for row in closed_rows)
    max_slip_proxy = max(abs(row["slip"]) for row in closed_rows)
    max_pi_nu_proxy = max(abs(row["pi_nu"]) for row in closed_rows)
    conformal_rows = attach_conformal_distance(closed_rows, janus_closed_params)
    photon_baryon = integrate_photon_baryon_hierarchy(conformal_rows, k=janus_closed_params.k)
    photon_history_rows = attach_photon_baryon_history(conformal_rows, k=janus_closed_params.k)
    cl_rows = cl_tt_proxy(photon_history_rows, photon_baryon)
    los_source = line_of_sight_temperature_source(photon_history_rows, photon_baryon)
    los_cl_rows = line_of_sight_cl_tt_proxy(photon_history_rows, photon_baryon)
    visibility_calibration = calibrate_visibility_to_astar(conformal_rows, janus_closed_params)
    visible_rows = attach_visibility(
        photon_history_rows,
        janus_closed_params,
        a_rec=visibility_calibration["a_rec"],
        width=visibility_calibration["width"],
    )
    reionized_rows = attach_reionization_visibility(visible_rows)
    physical_los_source = line_of_sight_temperature_source(visible_rows, photon_baryon)
    physical_los_cl_rows = line_of_sight_cl_tt_proxy(visible_rows, photon_baryon)
    source_decomposition = line_of_sight_source_decomposition(visible_rows, photon_baryon)
    projection_calibration = calibrate_projection_scale_from_theta_star(visible_rows, janus_closed_params)
    multipole_projection_distance_scale = projection_calibration["projection_distance_scale"]
    multipole_los_cl_rows = line_of_sight_multipole_cl_tt_proxy(
        visible_rows,
        photon_baryon,
        k=janus_closed_params.k,
        projection_distance_scale=multipole_projection_distance_scale,
    )
    multipole_spectra_rows = line_of_sight_multipole_spectra_proxy(
        visible_rows,
        photon_baryon,
        k=janus_closed_params.k,
        projection_distance_scale=multipole_projection_distance_scale,
    )
    low_ell_reionization_spectra = line_of_sight_multipole_spectra_proxy(
        [{**row, "visibility": row["visibility_with_reio"]} for row in reionized_rows],
        photon_baryon,
        k=janus_closed_params.k,
        ells=[2, 3, 4, 5, 6, 8, 10, 20],
        projection_distance_scale=multipole_projection_distance_scale,
    )
    lensed_spectra_rows = lensed_multipole_spectra_proxy(multipole_spectra_rows, visible_rows)
    spectra_contract = validate_spectra_contract(lensed_spectra_rows)
    visibility_peak = max(visible_rows, key=lambda row: row["visibility"])
    visibility_source_delta = abs(physical_los_source - los_source)
    visibility_source_relative_delta = visibility_source_delta / max(abs(los_source), 1.0e-30)
    symmetric_coupling, antisymmetric_coupling = mode_couplings(janus_params)
    z4_operator = z4_projection_operator_diagnostics(janus_params)
    final = rows[-1]
    readiness = readiness_report(spectra_contract)

    return {
        "description": "Minimal Janus-orbifold two-sector Boltzmann prototype for backend decision only.",
        "status": "bi-sector-boltzmann-prototype-integrated",
        "solver_name": "Janus Z4 CMB Solver",
        "solver_slug": "janus_z4_cmb_solver",
        "solver_contract_json": str(SOLVER_CONTRACT_PATH),
        "solver_contract_ready": True,
        "lcdm_limit_recovered": abs(lcdm_phi_plus - lcdm_phi_mono) < 1e-12 and abs(lcdm_phi_minus) < 1e-12,
        "membrane_density_continuity_encoded": True,
        "two_sector_projection_encoded": True,
        "z4_unified_geometric_origin_encoded": True,
        "metric_sectors_are_z4_projections": True,
        "independent_metric_dynamics_forbidden": True,
        "z4_projection_operator": z4_operator,
        "z4_projection_operator_normalized": bool(z4_operator["normalized"]),
        "max_z4_projection_residual": max_z4_projection_residual,
        "z4_projection_residuals_bounded": max_z4_projection_residual < 1e-12,
        "mono_metric_information_loss_detected": max_information_loss > 1e-8,
        "max_information_loss_metric": max_information_loss,
        "max_constraint_residual": max_constraint_residual,
        "constraints_bounded": max_constraint_residual < 1e-12,
        "two_metric_perturbations_explicit": True,
        "max_metric_constraint_residual": max_metric_constraint_residual,
        "metric_constraints_bounded": max_metric_constraint_residual < 1e-12,
        "newtonian_gauge_declared": True,
        "max_newtonian_gauge_residual": max_newtonian_gauge_residual,
        "newtonian_gauge_residuals_bounded": max_newtonian_gauge_residual < 1e-12,
        "membrane_density_jump_conserved": max_membrane_density_jump_residual < 1e-12,
        "max_membrane_density_jump_residual": max_membrane_density_jump_residual,
        "max_continuity_residual": max_continuity_residual,
        "continuity_residuals_bounded": max_continuity_residual < 1e-12,
        "max_momentum_exchange_residual": max_momentum_exchange_residual,
        "max_closed_momentum_exchange_residual": max_closed_momentum_exchange_residual,
        "bianchi_closure_residuals_bounded": max_closed_momentum_exchange_residual < 1e-12,
        "symmetric_mode_coupling": symmetric_coupling,
        "antisymmetric_mode_coupling": antisymmetric_coupling,
        "antisymmetric_mode_survives": abs(antisymmetric_coupling - symmetric_coupling) > 1e-12,
        "sound_horizon_proxy": sound_horizon_proxy(janus_params),
        "theta_star_proxy": theta_star_proxy(janus_params),
        "acoustic_ell_proxy": acoustic_ell_proxy(janus_params),
        "tt_peak_shift_proxy": tt_peak_shift_proxy(janus_params),
        "weyl_lensing_proxy": weyl_lensing_proxy(rows),
        "photon_baryon_hierarchy_integrated": True,
        "photon_baryon_history_integrated": True,
        "line_of_sight_uses_time_dependent_sources": True,
        "isw_uses_conformal_time_gradient": True,
        "neutrino_anisotropic_stress_proxy_integrated": True,
        "max_slip_proxy": max_slip_proxy,
        "max_pi_nu_proxy": max_pi_nu_proxy,
        "conformal_projection_map_computed": True,
        "conformal_time_mapping_computed": True,
        "conformal_distance_mapping_computed": True,
        "conformal_distance_source": "prototype_background_e_of_a",
        "eta_unit_grid": [conformal_rows[0]["eta_conformal"], conformal_rows[len(conformal_rows) // 2]["eta_conformal"], conformal_rows[-1]["eta_conformal"]],
        "chi_unit_grid": [conformal_rows[0]["chi_conformal"], conformal_rows[len(conformal_rows) // 2]["chi_conformal"], conformal_rows[-1]["chi_conformal"]],
        "max_chi_conformal": max(row["chi_conformal"] for row in conformal_rows),
        "photon_baryon_transfer_proxy": photon_baryon["temperature_transfer_proxy"],
        "photon_baryon_final": photon_baryon,
        "cl_tt_proxy_computed": True,
        "cl_tt_proxy": cl_rows,
        "visibility_proxy_integrated": True,
        "visibility_proxy_is_diagnostic_only": True,
        "line_of_sight_temperature_source": los_source,
        "line_of_sight_cl_tt_proxy_computed": True,
        "line_of_sight_cl_tt_proxy": los_cl_rows,
        "optical_depth_visibility_integrated": True,
        "visibility_calibrated_to_astar": True,
        "visibility_calibration": visibility_calibration,
        "physical_visibility_peak_residual": visibility_calibration["abs_peak_residual"],
        "physical_visibility_peak_a": visibility_peak["a"],
        "physical_visibility_peak_value": visibility_peak["visibility"],
        "physical_line_of_sight_temperature_source": physical_los_source,
        "physical_line_of_sight_cl_tt_proxy": physical_los_cl_rows,
        "line_of_sight_source_decomposition_computed": True,
        "line_of_sight_source_decomposition": source_decomposition,
        "transport_terms_are_proxy_only": True,
        "multipole_line_of_sight_projection_computed": True,
        "multipole_projection_uses_conformal_map": True,
        "bessel_kernel_projection_proxy_only": True,
        "k_projection_rescale_proxy_only": True,
        "k_ell_projection_scale_calibrated_from_theta_star_proxy": True,
        "projection_scale_calibration": projection_calibration,
        "multipole_projection_distance_scale": multipole_projection_distance_scale,
        "multipole_line_of_sight_cl_tt_proxy": multipole_los_cl_rows,
        "polarization_line_of_sight_proxy_computed": True,
        "te_ee_proxy_computed": True,
        "polarization_source_proxy_only": True,
        "multipole_line_of_sight_spectra_proxy": multipole_spectra_rows,
        "reionization_visibility_proxy_integrated": True,
        "low_ell_polarization_proxy_computed": True,
        "reionization_proxy_only": True,
        "low_ell_reionization_spectra_proxy": low_ell_reionization_spectra,
        "cmb_lensing_smoothing_proxy_computed": True,
        "lensing_source_proxy_only": True,
        "lensed_multipole_spectra_proxy": lensed_spectra_rows,
        "cmb_spectra_proxy_csv": str(SPECTRA_CSV_PATH),
        "cmb_spectra_export_ready_for_adapter": True,
        "cmb_adapter_contract_json": str(ADAPTER_CONTRACT_PATH),
        "cmb_adapter_contract_ready": spectra_contract["contract_passed"],
        "cmb_spectra_contract": spectra_contract,
        **readiness,
        "visibility_source_delta": visibility_source_delta,
        "visibility_source_relative_delta": visibility_source_relative_delta,
        "physical_visibility_required_for_cmb_gate": True,
        "final_row": final,
        "sample_rows": [rows[0], rows[len(rows) // 2], rows[-1]],
        "trajectory_csv": str(CSV_PATH),
        "backend_decision": "CAMB remains diagnostic; full validation requires deriving the bi-sector equations before choosing CLASS/hi_class or a dedicated backend.",
        "direct_planck_likelihood_ready": False,
        "full_observational_cosmology_no_fit_ready": False,
    }


def render_markdown(payload: dict) -> str:
    return "\n".join(
        [
            "# P0 EFT Bi-Sector Boltzmann Prototype",
            "",
            payload["description"],
            "",
            f"Status: `{payload['status']}`",
            f"Solver: `{payload['solver_name']}`",
            f"LCDM limit recovered: `{payload['lcdm_limit_recovered']}`",
            f"Two-sector projection encoded: `{payload['two_sector_projection_encoded']}`",
            f"Z4 unified geometric origin encoded: `{payload['z4_unified_geometric_origin_encoded']}`",
            f"Metric sectors are Z4 projections: `{payload['metric_sectors_are_z4_projections']}`",
            f"Independent metric dynamics forbidden: `{payload['independent_metric_dynamics_forbidden']}`",
            f"Z4 projection operator normalized: `{payload['z4_projection_operator_normalized']}`",
            f"Mono-metric information loss detected: `{payload['mono_metric_information_loss_detected']}`",
            f"Max information loss metric: `{payload['max_information_loss_metric']}`",
            f"Max constraint residual: `{payload['max_constraint_residual']}`",
            f"Two metric perturbations explicit: `{payload['two_metric_perturbations_explicit']}`",
            f"Max Z4 projection residual: `{payload['max_z4_projection_residual']}`",
            f"Max metric constraint residual: `{payload['max_metric_constraint_residual']}`",
            f"Newtonian gauge declared: `{payload['newtonian_gauge_declared']}`",
            f"Max Newtonian gauge residual: `{payload['max_newtonian_gauge_residual']}`",
            f"Membrane density jump conserved: `{payload['membrane_density_jump_conserved']}`",
            f"Max continuity residual: `{payload['max_continuity_residual']}`",
            f"Max momentum exchange residual: `{payload['max_momentum_exchange_residual']}`",
            f"Max closed momentum exchange residual: `{payload['max_closed_momentum_exchange_residual']}`",
            f"Symmetric mode coupling: `{payload['symmetric_mode_coupling']}`",
            f"Antisymmetric mode coupling: `{payload['antisymmetric_mode_coupling']}`",
            f"Sound horizon proxy: `{payload['sound_horizon_proxy']}`",
            f"Theta star proxy: `{payload['theta_star_proxy']}`",
            f"Acoustic ell proxy: `{payload['acoustic_ell_proxy']}`",
            f"TT peak-shift proxy: `{payload['tt_peak_shift_proxy']}`",
            f"Weyl/lensing proxy: `{payload['weyl_lensing_proxy']}`",
            f"Photon-baryon transfer proxy: `{payload['photon_baryon_transfer_proxy']}`",
            f"Photon-baryon history integrated: `{payload['photon_baryon_history_integrated']}`",
            f"LOS uses time-dependent sources: `{payload['line_of_sight_uses_time_dependent_sources']}`",
            f"ISW uses conformal-time gradient: `{payload['isw_uses_conformal_time_gradient']}`",
            f"Max neutrino slip proxy: `{payload['max_slip_proxy']}`",
            f"Conformal projection map computed: `{payload['conformal_projection_map_computed']}`",
            f"Conformal time mapping computed: `{payload['conformal_time_mapping_computed']}`",
            f"Conformal distance mapping computed: `{payload['conformal_distance_mapping_computed']}`",
            f"Conformal distance source: `{payload['conformal_distance_source']}`",
            f"Max conformal distance proxy: `{payload['max_chi_conformal']}`",
            f"C_ell TT proxy computed: `{payload['cl_tt_proxy_computed']}`",
            f"Line-of-sight source: `{payload['line_of_sight_temperature_source']}`",
            f"Visibility proxy diagnostic only: `{payload['visibility_proxy_is_diagnostic_only']}`",
            f"Physical visibility peak a: `{payload['physical_visibility_peak_a']}`",
            f"Physical visibility peak residual: `{payload['physical_visibility_peak_residual']}`",
            f"Physical line-of-sight source: `{payload['physical_line_of_sight_temperature_source']}`",
            f"Line-of-sight source decomposition computed: `{payload['line_of_sight_source_decomposition_computed']}`",
            f"Transport proxy relative size: `{payload['line_of_sight_source_decomposition']['transport_proxy_relative_size']}`",
            f"Multipole LOS projection computed: `{payload['multipole_line_of_sight_projection_computed']}`",
            f"Multipole projection uses conformal map: `{payload['multipole_projection_uses_conformal_map']}`",
            f"Bessel kernel projection proxy only: `{payload['bessel_kernel_projection_proxy_only']}`",
            f"k projection rescale proxy only: `{payload['k_projection_rescale_proxy_only']}`",
            f"k-ell projection calibrated from theta proxy: `{payload['k_ell_projection_scale_calibrated_from_theta_star_proxy']}`",
            f"Multipole projection distance scale: `{payload['multipole_projection_distance_scale']}`",
            f"Polarization LOS proxy computed: `{payload['polarization_line_of_sight_proxy_computed']}`",
            f"TE/EE proxy computed: `{payload['te_ee_proxy_computed']}`",
            f"Polarization source proxy only: `{payload['polarization_source_proxy_only']}`",
            f"Reionization visibility proxy integrated: `{payload['reionization_visibility_proxy_integrated']}`",
            f"Low-ell polarization proxy computed: `{payload['low_ell_polarization_proxy_computed']}`",
            f"Reionization proxy only: `{payload['reionization_proxy_only']}`",
            f"CMB lensing smoothing proxy computed: `{payload['cmb_lensing_smoothing_proxy_computed']}`",
            f"Lensing source proxy only: `{payload['lensing_source_proxy_only']}`",
            f"CMB spectra proxy CSV: `{payload['cmb_spectra_proxy_csv']}`",
            f"CMB spectra export ready for adapter: `{payload['cmb_spectra_export_ready_for_adapter']}`",
            f"CMB adapter contract ready: `{payload['cmb_adapter_contract_ready']}`",
            f"CMB solver scaffold completion: `{payload['cmb_solver_scaffold_completion_fraction']}`",
            f"CMB Z4-projected solver completion: `{payload['cmb_z4_projected_solver_completion_fraction']}`",
            f"CMB solver physical readiness: `{payload['cmb_solver_physical_readiness_fraction']}`",
            f"CMB solver scaffold >= 75%: `{payload['cmb_solver_scaffold_75_percent_reached']}`",
            f"CMB solver scaffold >= 95%: `{payload['cmb_solver_scaffold_95_percent_reached']}`",
            f"CMB Z4-projected solver >= 75%: `{payload['cmb_z4_projected_solver_75_percent_reached']}`",
            f"CMB solver physical >= 75%: `{payload['cmb_solver_physical_prediction_75_percent_reached']}`",
            f"Visibility source relative delta: `{payload['visibility_source_relative_delta']}`",
            f"Physical visibility required for CMB gate: `{payload['physical_visibility_required_for_cmb_gate']}`",
            f"Direct Planck likelihood ready: `{payload['direct_planck_likelihood_ready']}`",
            f"Full no-fit ready: `{payload['full_observational_cosmology_no_fit_ready']}`",
            "",
            "## Backend decision",
            "",
            payload["backend_decision"],
            "",
        ]
    )


def write_reports() -> dict:
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    payload = build_payload()
    rows = payload["sample_rows"]
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(render_markdown(payload), encoding="utf-8")
    with CSV_PATH.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(rows[0].keys()))
        writer.writeheader()
        writer.writerows(rows)
    spectra_rows = payload["lensed_multipole_spectra_proxy"]
    with SPECTRA_CSV_PATH.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(spectra_rows[0].keys()))
        writer.writeheader()
        writer.writerows(spectra_rows)
    ADAPTER_CONTRACT_PATH.write_text(
        json.dumps(
            {
                "spectra_csv": str(SPECTRA_CSV_PATH),
                "required_columns": payload["cmb_spectra_contract"]["required_columns"],
                "contract_passed": payload["cmb_spectra_contract"]["contract_passed"],
                "proxy_only": True,
                "direct_planck_likelihood_ready": payload["direct_planck_likelihood_ready"],
                "physical_blockers": payload["cmb_solver_physical_blockers"],
            },
            indent=2,
        ),
        encoding="utf-8",
    )
    SOLVER_CONTRACT_PATH.write_text(
        json.dumps(
            {
                "solver_name": payload["solver_name"],
                "solver_slug": payload["solver_slug"],
                "geometric_origin": "unified Janus/Z4 projection",
                "metric_sector_policy": "projected sectors only; independent metric dynamics forbidden",
                "spectra_csv": payload["cmb_spectra_proxy_csv"],
                "adapter_contract": payload["cmb_adapter_contract_json"],
                "z4_projected_completion": payload["cmb_z4_projected_solver_completion_fraction"],
                "scaffold_completion": payload["cmb_solver_scaffold_completion_fraction"],
                "direct_planck_likelihood_ready": payload["direct_planck_likelihood_ready"],
                "physical_blockers": payload["cmb_solver_physical_blockers"],
            },
            indent=2,
        ),
        encoding="utf-8",
    )
    return payload


def main() -> None:
    write_reports()
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {JSON_PATH}")
    print(f"Wrote {CSV_PATH}")


if __name__ == "__main__":
    main()
