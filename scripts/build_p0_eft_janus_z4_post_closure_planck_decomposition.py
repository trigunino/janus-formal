from __future__ import annotations

from pathlib import Path
import json
import math


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_post_closure_planck_decomposition.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_post_closure_planck_decomposition.json")
REPORT_DIR = Path("outputs/reports")

INPUTS = {
    "master": "p0_eft_janus_z4_cmb_diagnostic_master_report.json",
    "shape": "p0_eft_janus_z4_shape_diagnostic.json",
    "peak": "p0_eft_janus_z4_peak_damping_diagnostic.json",
    "lowtt": "p0_eft_janus_z4_lowtt_component_diagnostic.json",
    "lensing": "p0_eft_janus_z4_lensing_amplitude_diagnostic.json",
    "official": "p0_eft_janus_z4_official_planck_verdict.json",
    "phase_kernel": "p0_eft_janus_z4_acoustic_polarization_phase_kernel.json",
    "tight_quadrupole_identity": "p0_eft_janus_z4_tight_coupling_quadrupole_identity.json",
    "phase_application": "p0_eft_janus_z4_phase_kernel_application_diagnostic.json",
    "parity_mixer": "p0_eft_janus_z4_parity_polarization_mixer.json",
    "membrane_transport": "p0_eft_janus_z4_membrane_polarization_transport.json",
    "geometric_idea_screen": "p0_eft_janus_z4_geometric_cmb_idea_screen.json",
}


def _load(name: str) -> dict:
    return json.loads((REPORT_DIR / name).read_text(encoding="utf-8"))


def _severity(value: float | None) -> str:
    if value is None or not math.isfinite(value):
        return "rejected_or_unavailable"
    if value > 1.0e5:
        return "catastrophic"
    if value > 1.0e3:
        return "severe"
    if value > 100.0:
        return "large"
    return "moderate"


def build_payload() -> dict:
    reports = {key: _load(path) for key, path in INPUTS.items()}
    master = reports["master"]
    shape = reports["shape"]
    peak = reports["peak"]
    lowtt = reports["lowtt"]
    lensing = reports["lensing"]
    official = reports["official"]
    phase_kernel = reports["phase_kernel"]
    tight_quad = reports["tight_quadrupole_identity"]
    phase_application = reports["phase_application"]
    parity_mixer = reports["parity_mixer"]
    membrane_transport = reports["membrane_transport"]
    geometric_idea_screen = reports["geometric_idea_screen"]

    finite = official.get("finite_channel_chi2", {})
    bands = shape.get("bands", {})
    lowtt_frac = lowtt.get("mean_component_fractions", {})

    channel_decomposition = {
        "highl_TT": {
            "official_chi2": finite.get("highl_highl_TT"),
            "severity": _severity(finite.get("highl_highl_TT")),
            "shape_proxy": bands.get("highl_TT_peak1", {}),
            "candidate_physics": [
                "acoustic monopole/Doppler phase mismatch after Z4 source projection",
                "Silk damping normalization too steep or misplaced",
                "scalar source profile improves low-l only at cost of high-l TT",
            ],
        },
        "highl_TE": {
            "official_chi2": None,
            "severity": shape.get("worst_band"),
            "shape_proxy": bands.get("highl_TE", {}),
            "candidate_physics": [
                "temperature-polarization phase still wrong after coefficient transport",
                "active shear source lacks a derived quadrupole hierarchy with correct TE zero crossings",
                "spin-2 E projection is present but source phase is not observationally aligned",
            ],
        },
        "highl_EE": {
            "official_chi2": None,
            "severity": _severity(bands.get("highl_EE", {}).get("chi2_shape")),
            "shape_proxy": bands.get("highl_EE", {}),
            "candidate_physics": [
                "polarization amplitude/phase hierarchy remains observationally wrong",
                "visibility width and quadrupole generation need joint derivation, not independent scaling",
            ],
        },
        "low_l_TT": {
            "official_chi2": "rejected_or_infinite",
            "severity": "rejected",
            "component_fractions": lowtt_frac,
            "candidate_physics": [
                "SW auto-power dominates low-l TT",
                "ISW contribution and destructive interference remain too large",
                "time evolution of unified Z4 potentials needs a conservation/regularity constraint",
            ],
        },
        "low_l_EE": {
            "official_chi2": finite.get("lowlevel_lowl_EE"),
            "severity": _severity(finite.get("lowlevel_lowl_EE")),
            "candidate_physics": [
                "reionization/visibility tail is not yet a calibrated physical Z4 history",
                "large-scale E-mode source inherits polarization hierarchy mismatch",
            ],
        },
        "lensing": {
            "official_chi2": finite.get("lowlevel_lensing"),
            "severity": _severity(finite.get("lowlevel_lensing")),
            "amplitude_scan_best": lensing.get("best", {}),
            "candidate_physics": [
                "amplitude-only scaling is insufficient",
                "Z4 Weyl projection kernel shape is wrong over L range, not just normalization",
                "positive-photon geodesic map may require nonlocal optical projection, not local Weyl source only",
            ],
        },
    }

    priority_order = [
        "highl_TE",
        "highl_TT",
        "low_l_TT",
        "lensing",
        "highl_EE",
        "low_l_EE",
    ]

    phase_application_status = {
        "branch_only_diagnostic": bool(phase_application.get("branch_only_diagnostic")),
        "integration_recommended": bool(phase_application.get("integration_recommended")),
        "solver_numerics_modified": bool(phase_application.get("solver_numerics_modified")),
        "planck_validation_claimed": bool(phase_application.get("planck_validation_claimed")),
        "te_zero_crossing_count_delta": phase_application.get("deltas", {}).get("te_zero_crossing_count_delta"),
        "highl_te_chi2_per_dof_delta": phase_application.get("deltas", {}).get("highl_te_chi2_per_dof_delta"),
        "damped_integration_recommended": bool(phase_application.get("damped_integration_recommended")),
        "safe_solver_integration_recommended": bool(phase_application.get("safe_solver_integration_recommended")),
        "damped_te_zero_crossing_count_delta": phase_application.get("deltas", {}).get("damped_te_zero_crossing_count_delta"),
        "damped_highl_te_chi2_per_dof_delta": phase_application.get("deltas", {}).get("damped_highl_te_chi2_per_dof_delta"),
        "damped_highl_ee_chi2_per_dof_delta": phase_application.get("deltas", {}).get("damped_highl_ee_chi2_per_dof_delta"),
    }
    parity_mixer_status = {
        "branch_only_diagnostic": bool(parity_mixer.get("branch_only_diagnostic")),
        "safe_solver_integration_recommended": bool(parity_mixer.get("safe_solver_integration_recommended")),
        "solver_numerics_modified": bool(parity_mixer.get("solver_numerics_modified")),
        "planck_validation_claimed": bool(parity_mixer.get("planck_validation_claimed")),
        "viable_candidate_count": parity_mixer.get("viable_candidate_count"),
        "best_alpha_H": parity_mixer.get("best_candidate", {}).get("alpha_H"),
        "best_odd_sign": parity_mixer.get("best_candidate", {}).get("odd_sign"),
        "best_te_delta": parity_mixer.get("best_candidate", {}).get("score", {}).get("highl_te_chi2_per_dof_delta"),
        "best_ee_delta": parity_mixer.get("best_candidate", {}).get("score", {}).get("highl_ee_chi2_per_dof_delta"),
    }
    membrane_transport_status = {
        "branch_only_diagnostic": bool(membrane_transport.get("branch_only_diagnostic")),
        "safe_solver_integration_recommended": bool(membrane_transport.get("safe_solver_integration_recommended")),
        "solver_numerics_modified": bool(membrane_transport.get("solver_numerics_modified")),
        "planck_validation_claimed": bool(membrane_transport.get("planck_validation_claimed")),
        "a_sigma": membrane_transport.get("membrane", {}).get("a_sigma"),
        "z4_generator_angle": membrane_transport.get("z4_generator_angle"),
        "te_delta": membrane_transport.get("z4_quarter_turn", {}).get("score", {}).get("highl_te_chi2_per_dof_delta"),
        "ee_delta": membrane_transport.get("z4_quarter_turn", {}).get("score", {}).get("highl_ee_chi2_per_dof_delta"),
        "tt_unchanged": membrane_transport.get("z4_quarter_turn", {}).get("score", {}).get("tt_unchanged"),
    }
    geometric_screen_status = {
        "branch_only_diagnostic": bool(geometric_idea_screen.get("branch_only_diagnostic")),
        "no_continuous_fit_factor": bool(geometric_idea_screen.get("fixed_geometric_choices", {}).get("no_continuous_fit_factor")),
        "solver_numerics_modified": bool(geometric_idea_screen.get("solver_numerics_modified")),
        "planck_validation_claimed": bool(geometric_idea_screen.get("planck_validation_claimed")),
        "recommended_next_branches": geometric_idea_screen.get("recommended_next_branches", []),
        "eb_hidden_passes": bool(geometric_idea_screen.get("eb_hidden_conservation", {}).get("passes")),
        "weyl_projection_passes": bool(geometric_idea_screen.get("weyl_lensing_mirror_projection", {}).get("passes")),
        "swisw_memory_passes": bool(geometric_idea_screen.get("swisw_membrane_memory", {}).get("passes")),
    }

    next_priority = (
        "integrate Z4 membrane tetrad-transport polarization branch and run official gates"
        if membrane_transport_status["safe_solver_integration_recommended"]
        else
        "integrate Z4 parity/Holst polarization mixer into a controlled solver branch and run official gates"
        if parity_mixer_status["safe_solver_integration_recommended"]
        else
        "integrate damped tight quadrupole kernel into a controlled solver branch and re-run official gates"
        if phase_application_status["safe_solver_integration_recommended"]
        else "keep raw tight quadrupole as a TE-only probe; derive coupled EE visibility/recombination before solver integration"
        if phase_application_status["integration_recommended"]
        else "derive visibility/recombination or SW/ISW correction before integrating the tight quadrupole branch"
    )

    next_theory_correction = {
        "priority": next_priority,
        "why": (
            "The internal coefficient triad is closed, but high-l TE remains the worst shape band "
            "and TT/EE/lensing failures are consistent with a source-phase/projection problem rather "
            "than a missing scalar coefficient."
        ),
        "minimal_next_artifact": "P0EFTJanusZ4AcousticPolarizationPhaseKernel",
        "artifact_scaffold_ready": bool(phase_kernel.get("algebraic_phase_kernel_ready")),
        "tight_coupling_identity_derived": bool(tight_quad.get("tight_coupling_quadrupole_identity_derived")),
        "tight_quadrupole_report_used": bool(tight_quad),
        "phase_application_diagnostic_used": bool(phase_application),
        "phase_application_integration_recommended": phase_application_status["integration_recommended"],
        "damped_phase_application_integration_recommended": phase_application_status["damped_integration_recommended"],
        "safe_solver_integration_recommended": phase_application_status["safe_solver_integration_recommended"],
        "parity_mixer_safe_solver_integration_recommended": parity_mixer_status["safe_solver_integration_recommended"],
        "membrane_transport_safe_solver_integration_recommended": membrane_transport_status["safe_solver_integration_recommended"],
        "geometric_screen_recommended_next_branches": geometric_screen_status["recommended_next_branches"],
        "forbidden_shortcut": "do not tune E-mode scale, lensing amplitude, or scalar horizon scale as fitted nuisance parameters",
    }

    return {
        "status": "janus-z4-post-internal-closure-planck-decomposition",
        "inputs": INPUTS,
        "physical_closure_triad_ready": bool(master.get("physical_closure_triad_ready")),
        "official_planck_gate_passed": bool(master.get("official_planck_gate_passed")),
        "planck_validation_claimed": False,
        "solver_numerics_modified": False,
        "worst_shape_band": shape.get("worst_band"),
        "peak_phase_summary": {
            "max_tt_peak_shift": peak.get("max_tt_peak_shift"),
            "max_te_zero_shift": peak.get("max_te_zero_shift"),
            "te_zero_crossings_found": peak.get("te_zero_crossings_found"),
            "tt_damping_slope_residual": peak.get("tt_damping_slope", {}).get("slope_residual"),
        },
        "channel_decomposition": channel_decomposition,
        "priority_order": priority_order,
        "next_theory_correction": next_theory_correction,
        "phase_kernel_status": {
            "algebraic_phase_kernel_ready": bool(phase_kernel.get("algebraic_phase_kernel_ready")),
            "requires_tight_coupling_quadrupole_identity": not bool(tight_quad.get("tight_coupling_quadrupole_identity_derived")),
            "tight_coupling_quadrupole_identity_derived": bool(tight_quad.get("tight_coupling_quadrupole_identity_derived")),
            "planck_validation_claimed": bool(phase_kernel.get("planck_validation_claimed")),
        },
        "phase_application_status": phase_application_status,
        "parity_mixer_status": parity_mixer_status,
        "membrane_transport_status": membrane_transport_status,
        "geometric_screen_status": geometric_screen_status,
        "verdict": (
            "Post-closure internal Z4 coefficients are no longer the blocker. "
            "The current CMB failure is observational shape physics: acoustic/polarization phase, "
            "low-l potential time evolution and Weyl lensing projection."
        ),
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z4 Post-Closure Planck Decomposition",
        "",
        f"Status: `{payload['status']}`",
        f"Physical closure triad ready: `{payload['physical_closure_triad_ready']}`",
        f"Official Planck gate passed: `{payload['official_planck_gate_passed']}`",
        f"Solver numerics modified: `{payload['solver_numerics_modified']}`",
        f"Worst shape band: `{payload['worst_shape_band']}`",
        "",
        "## Priority Order",
    ]
    for item in payload["priority_order"]:
        lines.append(f"- `{item}`")
    lines.extend(["", "## Channel Decomposition"])
    for name, row in payload["channel_decomposition"].items():
        lines.append(f"- `{name}`: severity `{row['severity']}`, chi2 `{row.get('official_chi2')}`")
        for cause in row["candidate_physics"]:
            lines.append(f"  - {cause}")
    lines.extend([
        "",
        "## Next Theory Correction",
        f"- priority: {payload['next_theory_correction']['priority']}",
        f"- artifact: `{payload['next_theory_correction']['minimal_next_artifact']}`",
        f"- artifact scaffold ready: `{payload['next_theory_correction']['artifact_scaffold_ready']}`",
        f"- tight quadrupole report used: `{payload['next_theory_correction']['tight_quadrupole_report_used']}`",
        f"- tight-coupling identity derived: `{payload['next_theory_correction']['tight_coupling_identity_derived']}`",
        f"- phase application diagnostic used: `{payload['next_theory_correction']['phase_application_diagnostic_used']}`",
        f"- phase application integration recommended: `{payload['next_theory_correction']['phase_application_integration_recommended']}`",
        f"- damped phase application integration recommended: `{payload['next_theory_correction']['damped_phase_application_integration_recommended']}`",
        f"- safe solver integration recommended: `{payload['next_theory_correction']['safe_solver_integration_recommended']}`",
        f"- parity mixer safe solver integration recommended: `{payload['next_theory_correction']['parity_mixer_safe_solver_integration_recommended']}`",
        f"- membrane transport safe solver integration recommended: `{payload['next_theory_correction']['membrane_transport_safe_solver_integration_recommended']}`",
        f"- geometric screen recommended branches: `{payload['next_theory_correction']['geometric_screen_recommended_next_branches']}`",
        f"- forbidden shortcut: {payload['next_theory_correction']['forbidden_shortcut']}",
        "",
        "## Phase Application Status",
        f"- branch-only diagnostic: `{payload['phase_application_status']['branch_only_diagnostic']}`",
        f"- solver numerics modified: `{payload['phase_application_status']['solver_numerics_modified']}`",
        f"- Planck validation claimed: `{payload['phase_application_status']['planck_validation_claimed']}`",
        f"- safe solver integration recommended: `{payload['phase_application_status']['safe_solver_integration_recommended']}`",
        f"- TE zero crossing count delta: `{payload['phase_application_status']['te_zero_crossing_count_delta']}`",
        f"- high-l TE chi2/dof delta: `{payload['phase_application_status']['highl_te_chi2_per_dof_delta']}`",
        f"- damped TE zero crossing count delta: `{payload['phase_application_status']['damped_te_zero_crossing_count_delta']}`",
        f"- damped high-l TE chi2/dof delta: `{payload['phase_application_status']['damped_highl_te_chi2_per_dof_delta']}`",
        f"- damped high-l EE chi2/dof delta: `{payload['phase_application_status']['damped_highl_ee_chi2_per_dof_delta']}`",
        "",
        "## Parity Mixer Status",
        f"- branch-only diagnostic: `{payload['parity_mixer_status']['branch_only_diagnostic']}`",
        f"- safe solver integration recommended: `{payload['parity_mixer_status']['safe_solver_integration_recommended']}`",
        f"- viable candidates: `{payload['parity_mixer_status']['viable_candidate_count']}`",
        f"- best alpha_H: `{payload['parity_mixer_status']['best_alpha_H']}`",
        f"- best odd sign: `{payload['parity_mixer_status']['best_odd_sign']}`",
        f"- best TE chi2/dof delta: `{payload['parity_mixer_status']['best_te_delta']}`",
        f"- best EE chi2/dof delta: `{payload['parity_mixer_status']['best_ee_delta']}`",
        "",
        "## Membrane Transport Status",
        f"- branch-only diagnostic: `{payload['membrane_transport_status']['branch_only_diagnostic']}`",
        f"- safe solver integration recommended: `{payload['membrane_transport_status']['safe_solver_integration_recommended']}`",
        f"- a_sigma: `{payload['membrane_transport_status']['a_sigma']}`",
        f"- Z4 generator angle: `{payload['membrane_transport_status']['z4_generator_angle']}`",
        f"- TE chi2/dof delta: `{payload['membrane_transport_status']['te_delta']}`",
        f"- EE chi2/dof delta: `{payload['membrane_transport_status']['ee_delta']}`",
        f"- TT unchanged: `{payload['membrane_transport_status']['tt_unchanged']}`",
        "",
        "## Geometric Idea Screen",
        f"- no continuous fit factor: `{payload['geometric_screen_status']['no_continuous_fit_factor']}`",
        f"- recommended branches: `{payload['geometric_screen_status']['recommended_next_branches']}`",
        f"- E/B hidden passes: `{payload['geometric_screen_status']['eb_hidden_passes']}`",
        f"- Weyl projection passes: `{payload['geometric_screen_status']['weyl_projection_passes']}`",
        f"- SW/ISW memory passes: `{payload['geometric_screen_status']['swisw_memory_passes']}`",
        "",
        payload["verdict"],
        "",
    ])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
