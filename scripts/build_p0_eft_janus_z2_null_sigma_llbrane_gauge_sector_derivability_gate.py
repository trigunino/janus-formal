from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path(
    "outputs/reports/"
    "p0_eft_janus_z2_null_sigma_llbrane_gauge_sector_derivability_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/"
    "p0_eft_janus_z2_null_sigma_llbrane_gauge_sector_derivability_gate.json"
)


def build_payload() -> dict:
    derived_now = {
        "LL_worldvolume_has_auxiliary_gauge_channel": True,
        "chi_LL_is_modified_measure_composite": True,
        "gauge_EOM_conserves_dual_measure_flux_locally": True,
        "spherical_S2_flux_ansatz_is_consistent": True,
        "flux_law_can_quantize_sector_if_bundle_is_global": True,
        "PT_fixes_chi_sign_negative": True,
        "bridge_matching_gives_Rs_from_chi": True,
    }
    missing = {
        "global_LL_gauge_bundle_on_S2_throat_derived": False,
        "integer_flux_n_selected_or_declared_as_sector": False,
        "worldvolume_charge_quantum_q_LL_derived": False,
        "specific_Janus_LL_lagrangian_L_of_F2_derived": False,
        "on_shell_F2_0_derived_from_L_of_F2": False,
        "auxiliary_metric_to_physical_S2_area_gauge_derived": False,
    }
    formulae = {
        "modified_measure_tension": "chi_LL = Phi/sqrt(-gamma)",
        "local_tension_conservation": "d chi_LL = 0 away from charged defects",
        "flux_law_target": "integral_{S2} F_LL = 2*pi*n/q_LL",
        "SO3_flux": "F_theta_phi = B*sin(theta), B=n/(2*q_LL)",
        "area_gauge_dependent_F2": "F_ab F^ab = 2*B^2/R_s^4 only if physical S2 metric raises indices",
        "conditional_scale": "R_s = (2*B^2/F2_0)^(1/4)",
        "conditional_chi": "chi_LL = -1/(8*pi*R_s)",
    }
    return {
        "status": "janus-z2-null-sigma-llbrane-gauge-sector-derivability-gate",
        "active_core": "Z2_tunnel_Sigma",
        "branch": "Z2_null_Sigma_PT_bridge",
        "derived_now": derived_now,
        "missing_for_no_rustine_chi_selection": missing,
        "formulae": formulae,
        "four_physical_blocks": {
            "n_on_S2_throat": {
                "status": "target_only",
                "can_advance_without_new_action": (
                    "only to the conditional statement that n is an integer "
                    "if the LL gauge bundle is global on S2_throat"
                ),
                "hard_missing": [
                    "global_LL_gauge_bundle_on_S2_throat",
                    "bundle_pullback_from_Janus_null_worldvolume",
                ],
            },
            "q_LL": {
                "status": "not_derived",
                "can_advance_without_new_action": "no",
                "hard_missing": [
                    "normalization_of_worldvolume_gauge_kinetic_or_topological_term",
                    "minimal_charge_unit_or_coupling_convention",
                ],
            },
            "F2_0": {
                "status": "not_derived",
                "can_advance_without_new_action": "no",
                "hard_missing": [
                    "specific_L_of_F2",
                    "algebraic_on_shell_equation_from_dL_dF2",
                ],
            },
            "area_gauge": {
                "status": "not_derived",
                "can_advance_without_new_action": "partially",
                "hard_missing": [
                    "proof_that_auxiliary_gamma_ab_equals_or_projects_to_physical_induced_S2_metric",
                    "or_explicit_conversion_factor_between_gamma_area_and_physical_area",
                ],
            },
        },
        "no_rustine_verdict": (
            "Current Janus/LL data advance the algebra and identify the exact "
            "needed inputs, but do not derive q_LL, F2_0, or the physical area "
            "gauge. Any numeric chi_LL before these are derived is an extension "
            "state choice."
        ),
        "gate_passed": False,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2 Null Sigma LL-Brane Gauge Sector Derivability Gate",
        "",
        payload["no_rustine_verdict"],
        "",
        "## Derived Now",
    ]
    lines.extend(f"- `{key}`: `{value}`" for key, value in payload["derived_now"].items())
    lines.extend(["", "## Missing"])
    lines.extend(
        f"- `{key}`: `{value}`"
        for key, value in payload["missing_for_no_rustine_chi_selection"].items()
    )
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
