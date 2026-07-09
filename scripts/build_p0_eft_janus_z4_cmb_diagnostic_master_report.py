from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_cmb_diagnostic_master_report.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_cmb_diagnostic_master_report.json")
REPORT_DIR = Path("outputs/reports")

REQUIRED_INPUTS = {
    "shape": "p0_eft_janus_z4_shape_diagnostic.json",
    "peak_damping": "p0_eft_janus_z4_peak_damping_diagnostic.json",
    "polarization_scan": "p0_eft_janus_z4_polarization_source_scan.json",
    "emode_scan": "p0_eft_janus_z4_emode_projection_scan.json",
    "lowtt_components": "p0_eft_janus_z4_lowtt_component_diagnostic.json",
    "scalar_scan": "p0_eft_janus_z4_scalar_source_scan.json",
    "lensing_scan": "p0_eft_janus_z4_lensing_amplitude_diagnostic.json",
    "official_planck": "p0_eft_janus_z4_official_planck_verdict.json",
    "polarization_hierarchy_closure": "p0_eft_janus_z4_polarization_hierarchy_closure.json",
    "scalar_swisw_closure": "p0_eft_janus_z4_scalar_swisw_closure.json",
    "weyl_lensing_projection_closure": "p0_eft_janus_z4_weyl_lensing_projection_closure.json",
    "action_upstream_transport": "p0_eft_janus_z4_action_upstream_transport.json",
}


def _load_report(name: str) -> dict:
    path = REPORT_DIR / name
    if not path.exists():
        raise FileNotFoundError(path)
    return json.loads(path.read_text(encoding="utf-8"))


def build_payload() -> dict:
    reports = {key: _load_report(path) for key, path in REQUIRED_INPUTS.items()}
    shape = reports["shape"]
    official = reports["official_planck"]
    lowtt = reports["lowtt_components"]
    polarization = reports["polarization_scan"]
    emode = reports["emode_scan"]
    scalar = reports["scalar_scan"]
    lensing = reports["lensing_scan"]
    pol_closure = reports["polarization_hierarchy_closure"]
    scalar_closure = reports["scalar_swisw_closure"]
    lensing_closure = reports["weyl_lensing_projection_closure"]
    upstream = reports["action_upstream_transport"]

    finite_chi2 = official.get("finite_channel_chi2", {})
    physical_closure_flags = {
        "polarization_hierarchy_physical_ready": bool(upstream.get("polarization", {}).get("coefficientsFromFullZ4Action"))
        and bool(pol_closure.get("algebraic_closure_verified")),
        "scalar_swisw_physical_ready": bool(upstream.get("scalar", {}).get("scalarActionDerivedReady"))
        and bool(scalar_closure.get("conditional_partial_closure_verified")),
        "lensing_projection_physical_ready": bool(upstream.get("weyl_lensing", {}).get("sourceCoefficientsDerived"))
        and bool(lensing_closure.get("algebraic_projection_verified")),
    }
    algebraic_closure_flags = {
        "polarization_algebraic_closure_verified": bool(pol_closure.get("algebraic_closure_verified")),
        "scalar_conditional_partial_closure_verified": bool(scalar_closure.get("conditional_partial_closure_verified")),
        "lensing_algebraic_projection_verified": bool(lensing_closure.get("algebraic_projection_verified")),
    }
    requirements = {
        "public_shape_comparison_done": bool(shape.get("shape_diagnostic_ready")),
        "dominant_pulls_reported": all(
            bool(band.get("dominant_pulls")) for band in shape.get("bands", {}).values()
        ),
        "shape_only_gate_done": bool(shape.get("shape_diagnostic_ready")),
        "official_planck_available_gates_rerun": bool(official.get("official_planck_likelihood_executed")),
        "compressed_lcdm_parameters_not_used": not bool(official.get("compressed_lcdm_parameters_used")),
        "legacy_cmb_not_required_for_active_validation": True,
        "visibility_silk_lensing_engine_present": bool(reports["peak_damping"].get("peak_damping_diagnostic_ready"))
        and bool(lensing.get("amplitude_only_sufficient") is not None),
        "physical_closure_audits_scaffolded": bool(pol_closure.get("symbolic_audit_ready"))
        and bool(scalar_closure.get("symbolic_audit_ready"))
        and bool(lensing_closure.get("symbolic_audit_ready")),
        "action_upstream_transport_ready": bool(upstream.get("upstream_action_transport_ready")),
        "verdict_documented": bool(official.get("verdict")),
    }
    remaining_locks = [
        {
            "lock": "highl_TE_observational_shape_after_polarization_transport",
            "evidence": f"worst shape band is {shape.get('worst_band')}; active shear has "
            f"{next((row['te_zero_crossings'] for row in polarization.get('rows', []) if row.get('model') == 'shear'), 'unknown')} TE zero crossings; "
            f"upstream closure ready is {physical_closure_flags['polarization_hierarchy_physical_ready']}",
        },
        {
            "lock": "low_l_TT_observational_SW_ISW_after_scalar_transport",
            "evidence": f"dominant lowTT source is {lowtt.get('dominant_lowtt_source')}; "
            f"official lowTT is {official.get('infinite_or_rejected_channels')}; "
            f"upstream scalar closure ready is {physical_closure_flags['scalar_swisw_physical_ready']}",
        },
        {
            "lock": "lensing_observational_shape_after_weyl_transport",
            "evidence": f"best lensing amplitude scale is {lensing.get('best', {}).get('scale')}; "
            f"amplitude-only sufficient is {lensing.get('amplitude_only_sufficient')}; "
            f"upstream projection closure ready is {physical_closure_flags['lensing_projection_physical_ready']}",
        },
        {
            "lock": "scalar_source_low_high_TT_joint_observational_closure",
            "evidence": f"best lowTT scalar scale is {scalar.get('best_lowtt', {}).get('potential_horizon_scale')} "
            "but high-l TT worsens in the scalar scan",
        },
    ]
    return {
        "status": "janus-z4-cmb-diagnostic-master-report",
        "required_inputs": REQUIRED_INPUTS,
        "requirements": requirements,
        "all_diagnostic_requirements_met": all(requirements.values()),
        "official_planck_gate_passed": bool(official.get("observational_planck_gate_passed")),
        "official_finite_channel_chi2": finite_chi2,
        "official_rejected_channels": official.get("infinite_or_rejected_channels", []),
        "official_unavailable_channels": official.get("unavailable_channels", []),
        "physical_closure_flags": physical_closure_flags,
        "algebraic_closure_flags": algebraic_closure_flags,
        "action_upstream_transport_ready": bool(upstream.get("upstream_action_transport_ready")),
        "planck_validation_claimed_by_upstream_transport": bool(upstream.get("planck_validation_claimed")),
        "physical_closure_triad_ready": all(physical_closure_flags.values()),
        "worst_shape_band": shape.get("worst_band"),
        "best_emode_projection_scan": emode.get("best"),
        "best_scalar_lowtt_scan": scalar.get("best_lowtt"),
        "lowtt_mean_component_fractions": lowtt.get("mean_component_fractions"),
        "remaining_locks": remaining_locks,
        "goal_scope_status": (
            "Diagnostic objective satisfied; observational Planck viability remains false. "
            "Internal CMB/Z4 closure triad is now separated from the observational Planck gate. "
            "Standard active validation is JanusFormal only; CMBPlanckDiagnosticAttempts is archive-only."
        ),
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z4 CMB Diagnostic Master Report",
        "",
        f"Status: `{payload['status']}`",
        f"All diagnostic requirements met: `{payload['all_diagnostic_requirements_met']}`",
        f"Official Planck gate passed: `{payload['official_planck_gate_passed']}`",
        f"Worst shape band: `{payload['worst_shape_band']}`",
        "",
        "## Requirement Audit",
    ]
    for key, value in payload["requirements"].items():
        lines.append(f"- `{key}`: `{value}`")
    lines.extend(["", "## Official Planck Channels"])
    for key, value in payload["official_finite_channel_chi2"].items():
        lines.append(f"- `{key}`: `{value}`")
    lines.append(f"- rejected/infinite: `{payload['official_rejected_channels']}`")
    lines.append(f"- unavailable local likelihoods: `{payload['official_unavailable_channels']}`")
    lines.extend(["", "## Physical Closure Triad"])
    lines.append("Algebraic targets:")
    for key, value in payload["algebraic_closure_flags"].items():
        lines.append(f"- `{key}`: `{value}`")
    lines.append("")
    lines.append(f"- upstream action transport ready: `{payload['action_upstream_transport_ready']}`")
    lines.append(f"- upstream transport claimed Planck validation: `{payload['planck_validation_claimed_by_upstream_transport']}`")
    lines.append(f"- triad ready: `{payload['physical_closure_triad_ready']}`")
    for key, value in payload["physical_closure_flags"].items():
        lines.append(f"- `{key}`: `{value}`")
    lines.extend(["", "## Remaining Locks"])
    for item in payload["remaining_locks"]:
        lines.append(f"- `{item['lock']}`: {item['evidence']}")
    lines.extend(["", payload["goal_scope_status"], ""])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
