from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_cmb_failure_map.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_cmb_failure_map.json")
REPORT_DIR = Path("outputs/reports")

INPUTS = {
    "official": "p0_eft_janus_z4_integrated_negative_imprint_planck_gate.json",
    "post_closure": "p0_eft_janus_z4_post_closure_planck_decomposition.json",
    "shape": "p0_eft_janus_z4_shape_diagnostic.json",
    "lowtt": "p0_eft_janus_z4_lowtt_component_diagnostic.json",
    "lensing": "p0_eft_janus_z4_lensing_amplitude_diagnostic.json",
    "integrated_branch": "p0_eft_janus_z4_integrated_negative_imprint_branch.json",
    "tt_swisw_derivation": "p0_eft_janus_z4_tt_swisw_derivation.json",
    "tt_swisw_gate": "p0_eft_janus_z4_tt_swisw_planck_gate.json",
    "weyl_tt_derivation": "p0_eft_janus_z4_weyl_tt_transport_derivation.json",
    "weyl_tt_branch": "p0_eft_janus_z4_weyl_tt_transport_solver_branch.json",
}


def _load(name: str) -> dict:
    return json.loads((REPORT_DIR / name).read_text(encoding="utf-8"))


def build_payload() -> dict:
    reports = {key: _load(path) for key, path in INPUTS.items()}
    official = reports["official"]
    post = reports["post_closure"]
    shape = reports["shape"]
    lowtt = reports["lowtt"]
    lensing = reports["lensing"]
    integrated = reports["integrated_branch"]
    tt_swisw = reports["tt_swisw_derivation"]
    tt_swisw_gate = reports["tt_swisw_gate"]
    weyl_tt_derivation = reports["weyl_tt_derivation"]
    weyl_tt_branch = reports["weyl_tt_branch"]
    gate_delta = {
        key: (
            tt_swisw_gate.get("finite_channel_chi2", {}).get(key)
            - official.get("finite_channel_chi2", {}).get(key)
        )
        for key in ["lensing", "highl_TT", "highl_TTTEEE"]
        if key in tt_swisw_gate.get("finite_channel_chi2", {})
        and key in official.get("finite_channel_chi2", {})
    }

    obligations = [
        {
            "lock": "TT_acoustic_source_phase_and_damping",
            "planck_evidence": {
                "highl_TT": official["finite_channel_chi2"].get("highl_TT"),
                "highl_TTTEEE": official["finite_channel_chi2"].get("highl_TTTEEE"),
                "shape_band": "highl_TT_peak1",
                "integrated_delta_vs_controlled": integrated["deltas_vs_controlled_branch"].get("highl_TT_peak1"),
            },
            "equations_to_derive": [
                "Z4 photon-baryon monopole equation with negative-sector source term",
                "Doppler source transport under membrane tetrad projection",
                "Silk damping scale from Z4 recombination/visibility, not fitted smoothing",
                "Primordial imprint transfer kernel P_R(k)->P_R^Z4(k) derived from negative-sector Jeans scale",
            ],
            "observables": ["high-l TT", "high-l TTTEEE", "TT peak phase", "TT damping tail"],
            "scripts": [
                "scripts/build_p0_eft_janus_z4_native_cmb_transfer_solver.py",
                "scripts/build_p0_eft_janus_z4_integrated_negative_imprint_branch.py",
                "scripts/build_p0_eft_janus_z4_peak_damping_diagnostic.py",
                "scripts/build_p0_eft_janus_z4_tt_swisw_derivation.py",
            ],
            "derivation_status": tt_swisw["tt_acoustic_derivation"]["derived"],
        },
        {
            "lock": "low_l_SW_ISW_regularization",
            "planck_evidence": {
                "lowl_TT": official["channels"].get("lowl_TT", {}).get("chi2"),
                "dominant_lowtt_source": lowtt.get("dominant_lowtt_source"),
                "component_fractions": lowtt.get("mean_component_fractions"),
            },
            "equations_to_derive": [
                "Z4 scalar potential conservation law across radiation/matter transition",
                "regularity condition for Phi_dot+Psi_dot after membrane projection",
                "low-l Sachs-Wolfe and ISW source split with hidden-sector cancellation terms",
            ],
            "observables": ["low-l TT", "SW plateau", "early ISW", "late ISW"],
            "scripts": [
                "scripts/build_p0_eft_janus_z4_lowtt_component_diagnostic.py",
                "scripts/build_p0_eft_janus_z4_scalar_swisw_closure.py",
                "scripts/build_p0_eft_janus_z4_scalar_source_scan.py",
                "scripts/build_p0_eft_janus_z4_tt_swisw_derivation.py",
            ],
            "derivation_status": tt_swisw["swisw_regularization"]["derived"],
        },
        {
            "lock": "Weyl_lensing_projection_kernel",
            "planck_evidence": {
                "lensing": official["finite_channel_chi2"].get("lensing"),
                "amplitude_only_sufficient": lensing.get("amplitude_only_sufficient"),
                "best_amplitude_scale": lensing.get("best", {}).get("scale"),
            },
            "equations_to_derive": [
                "positive-photon geodesic projection through Z4/orbifold metric variables",
                "Weyl potential kernel C_L^{phiphi} with sector-projected line-of-sight distance",
                "mirror-sector Weyl source transport and normalization",
            ],
            "observables": ["Planck lensing C_L phiphi", "lensed TT/TE/EE smoothing", "Weyl potential shape"],
            "scripts": [
                "scripts/build_p0_eft_janus_z4_weyl_lensing_projection_closure.py",
                "scripts/build_p0_eft_janus_z4_lensing_amplitude_diagnostic.py",
                "src/janus_lab/z4_cmb_cobaya.py",
            ],
        },
        {
            "lock": "polarization_phase_and_visibility_guard",
            "planck_evidence": {
                "worst_shape_band": post.get("worst_shape_band"),
                "integrated_TE_delta_vs_controlled": integrated["deltas_vs_controlled_branch"].get("highl_TE"),
                "integrated_EE_delta_vs_controlled": integrated["deltas_vs_controlled_branch"].get("highl_EE"),
            },
            "equations_to_derive": [
                "tight-coupling quadrupole identity after Z4 parity transport",
                "visibility-width correction coupled to E-mode projection",
                "TE zero-crossing phase condition from common TT/E source clock",
            ],
            "observables": ["high-l TE", "high-l EE", "TE zero crossings", "E-mode damping tail"],
            "scripts": [
                "scripts/build_p0_eft_janus_z4_phase_kernel_application_diagnostic.py",
                "scripts/build_p0_eft_janus_z4_membrane_polarization_transport.py",
                "scripts/build_p0_eft_janus_z4_recombination_visibility_target.py",
            ],
        },
    ]
    return {
        "status": "janus-z4-cmb-failure-map",
        "inputs": INPUTS,
        "solver_numerics_modified": False,
        "planck_validation_claimed": False,
        "official_planck_gate_passed": False,
        "integrated_negative_imprint_rejected": not bool(official.get("observational_planck_gate_passed")),
        "tt_swisw_derivation_ready": bool(
            tt_swisw["tt_acoustic_derivation"]["derived"]
            and tt_swisw["swisw_regularization"]["derived"]
        ),
        "tt_swisw_planck_delta_vs_integrated_gate": gate_delta,
        "tt_swisw_branch_official_gate_passed": bool(tt_swisw_gate.get("observational_planck_gate_passed")),
        "weyl_tt_transport_derivation_ready": bool(
            weyl_tt_derivation["weyl_lensing_derivation"]["derived"]
            and weyl_tt_derivation["tt_transport_beyond_leading"]["derived"]
        ),
        "weyl_tt_transport_branch_safe_for_gate": bool(weyl_tt_branch.get("safe_for_official_gate")),
        "weyl_tt_transport_branch_deltas": weyl_tt_branch.get("deltas_vs_integrated_negative_imprint_branch", {}),
        "failure_obligations": obligations,
        "next_code_action": (
            "Both leading TT/SW-ISW and mirror-even Weyl/clock transport are insufficient. "
            "Next target is a coupled visibility/recombination plus TT phase derivation, not isolated source insertion."
        ),
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z4 CMB Failure Map",
        "",
        f"Status: `{payload['status']}`",
        f"Solver numerics modified: `{payload['solver_numerics_modified']}`",
        f"Planck validation claimed: `{payload['planck_validation_claimed']}`",
        f"Integrated negative imprint rejected: `{payload['integrated_negative_imprint_rejected']}`",
        f"TT/SW-ISW branch gate passed: `{payload['tt_swisw_branch_official_gate_passed']}`",
        f"TT/SW-ISW Planck delta vs integrated gate: `{payload['tt_swisw_planck_delta_vs_integrated_gate']}`",
        f"Weyl/TT transport derivation ready: `{payload['weyl_tt_transport_derivation_ready']}`",
        f"Weyl/TT transport branch safe for gate: `{payload['weyl_tt_transport_branch_safe_for_gate']}`",
        f"Weyl/TT transport deltas: `{payload['weyl_tt_transport_branch_deltas']}`",
        "",
        "## Obligations",
    ]
    for item in payload["failure_obligations"]:
        lines.append(f"### {item['lock']}")
        lines.append(f"- Planck evidence: `{item['planck_evidence']}`")
        lines.append(f"- Observables: `{item['observables']}`")
        if "derivation_status" in item:
            lines.append(f"- Derivation ready: `{item['derivation_status']}`")
        lines.append("- Equations to derive:")
        for eq in item["equations_to_derive"]:
            lines.append(f"  - {eq}")
        lines.append(f"- Scripts: `{item['scripts']}`")
    lines.extend(["", f"Next code action: {payload['next_code_action']}", ""])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
