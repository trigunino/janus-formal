from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_chi_ll_option_evaluation_matrix.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_chi_ll_option_evaluation_matrix.json")


def build_payload() -> dict:
    options = {
        "explicit_state_chi_LL": {
            "meaning_for_world": (
                "Our universe occupies one allowed null-bridge state sector; "
                "chi_LL is analogous to an ADM mass or initial charge."
            ),
            "no_fit_status": "extension_state_allowed_but_not_predicted",
            "required_theory_inputs": [
                "clean non-observational provenance for chi_LL_abs_inverse_m",
                "proof that chi_LL is conserved and PT-compatible",
            ],
            "can_predict_chi_LL": False,
            "observational_discriminator_after_theory": [
                "bridge-derived H0/R_s consistency",
                "BAO/CMB background once active observational solver exists",
            ],
        },
        "S2_flux_quantized_chi_LL": {
            "meaning_for_world": (
                "The throat sector is quantized; our universe is labelled by an "
                "integer flux n on S2_throat."
            ),
            "no_fit_status": "best_candidate_for_discrete_prediction",
            "required_theory_inputs": [
                "global LL gauge bundle on S2_throat",
                "integer flux sector n",
                "q_LL",
                "F2_0",
                "physical induced S2 area gauge",
            ],
            "can_predict_chi_LL": "conditional",
            "observational_discriminator_after_theory": [
                "discrete allowed R_s/M_bridge ladder",
                "whether any n gives positive Friedmann source without retuning",
            ],
        },
        "Souriau_Noether_mass_orbit": {
            "meaning_for_world": (
                "The throat tension is the local image of a global Souriau/Noether "
                "mass orbit; PT maps M_plus to -M_plus."
            ),
            "no_fit_status": "charge_framework_ready_orbit_not_selected",
            "required_theory_inputs": [
                "active coadjoint orbit or Hamiltonian moment-map value",
                "mass Casimir in SI units",
                "moment-map conservation on Janus Z2/PT state",
            ],
            "can_predict_chi_LL": "conditional",
            "observational_discriminator_after_theory": [
                "global mass -> R_s -> chi_LL -> background source",
                "consistency with PT paired mass sector",
            ],
        },
        "minimal_LL_gauge_action": {
            "meaning_for_world": (
                "The bridge has its own microscopic worldvolume gauge dynamics; "
                "chi_LL follows from a chosen/adopted L(F2)."
            ),
            "no_fit_status": "new_physical_extension_if_action_is_adopted",
            "required_theory_inputs": [
                "explicit L(F2)",
                "variation giving F2_0",
                "gauge normalization giving q_LL",
                "proof of well-posed null-boundary variational principle",
            ],
            "can_predict_chi_LL": "yes_if_action_fixes_q_and_F2_0",
            "observational_discriminator_after_theory": [
                "derived chi_LL(n) spectrum",
                "stability and sign of LL stress tensor",
            ],
        },
        "UV_scale_chi_LL": {
            "meaning_for_world": (
                "The throat scale is microscopic; chi_LL is fixed by Planck/Holst/"
                "torsion/quantum-gravity data, not by cosmological state."
            ),
            "no_fit_status": "blocked_until_UV_identification_theorem",
            "required_theory_inputs": [
                "theorem identifying R_s or ell_collar with a UV length",
                "Holst/Immirzi or torsion scale with dimensions",
                "proof this scale enters the null throat action",
            ],
            "can_predict_chi_LL": "conditional",
            "observational_discriminator_after_theory": [
                "whether UV throat can affect macroscopic Friedmann source",
                "early-universe relic/initial-condition signature",
            ],
        },
    }
    ranking = [
        "S2_flux_quantized_chi_LL",
        "minimal_LL_gauge_action",
        "Souriau_Noether_mass_orbit",
        "explicit_state_chi_LL",
        "UV_scale_chi_LL",
    ]
    return {
        "status": "janus-z2-chi-ll-option-evaluation-matrix",
        "active_core": "Z2_tunnel_Sigma",
        "purpose": "compare non-rustine ways to close or interpret chi_LL",
        "options": options,
        "recommended_order": ranking,
        "observation_policy": {
            "use_observations_to_choose_free_chi_LL": False,
            "use_observations_after_theory_closure": True,
            "required_before_observations": [
                "theory route writes chi_LL or R_s with non-observational provenance",
                "active Z2/Sigma observational equations are generated",
                "no reuse of legacy Z4/Planck compressed gates",
            ],
        },
        "next_concrete_routes": [
            "derive_or_adopt_minimal_LL_gauge_action_L_of_F2",
            "derive_flux_quantization_inputs_q_LL_F2_0_area_gauge",
            "derive_Souriau_orbit_mass_if_global_route_is_preferred",
        ],
        "gate_passed": True,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2 chi_LL Option Evaluation Matrix",
        "",
        "Observation policy:",
        f"- use observations to choose free chi_LL: `{payload['observation_policy']['use_observations_to_choose_free_chi_LL']}`",
        f"- use observations after theory closure: `{payload['observation_policy']['use_observations_after_theory_closure']}`",
        "",
        "## Recommended Order",
    ]
    lines.extend(f"{idx}. `{name}`" for idx, name in enumerate(payload["recommended_order"], start=1))
    lines.extend(["", "## Options"])
    for name, data in payload["options"].items():
        lines.extend(
            [
                f"### `{name}`",
                f"- meaning: {data['meaning_for_world']}",
                f"- status: `{data['no_fit_status']}`",
                f"- can predict chi_LL: `{data['can_predict_chi_LL']}`",
            ]
        )
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
