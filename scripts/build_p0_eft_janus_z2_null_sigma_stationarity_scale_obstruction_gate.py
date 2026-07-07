from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.janus_lab.z2_null_sigma_generator_normalization import (
    null_sigma_generator_normalization_payload,
)
from src.janus_lab.z2_null_sigma_pt_transverse_pullback import (
    null_sigma_pt_transverse_pullback_payload,
)
from src.janus_lab.z2_null_sigma_variation_reduction import (
    null_sigma_variation_reduction_payload,
)


REPORT_PATH = Path(
    "outputs/reports/"
    "p0_eft_janus_z2_null_sigma_stationarity_scale_obstruction_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/"
    "p0_eft_janus_z2_null_sigma_stationarity_scale_obstruction_gate.json"
)


def build_payload(rs: float = 1.0) -> dict:
    variation = null_sigma_variation_reduction_payload(rs)
    pullback = null_sigma_pt_transverse_pullback_payload(rs)
    generator = null_sigma_generator_normalization_payload(rs)
    radial_coeff = variation["radial_reduction"][
        "delta_density_coefficient_over_sin_theta"
    ]
    closure = {
        "null_density_radial_variation_reduced": variation[
            "bulk_null_density_variation_reduced"
        ],
        "PT_stress_slots_available": pullback["active_stress_mapping_ready"],
        "generator_rescaling_fixed": generator[
            "null_generator_rescaling_quotiented"
        ],
        "radial_stationarity_equation_available": True,
        "radial_stationarity_equation_sets_finite_Rs": False,
        "external_mass_or_state_charge_available": False,
    }
    return {
        "status": "janus-z2-null-sigma-stationarity-scale-obstruction-gate",
        "active_core": "Z2_tunnel_Sigma",
        "branch": "Z2_null_Sigma_PT_bridge",
        "rs_unit": rs,
        "stationarity_equation": "delta(sqrt(q) kappa_l + joint_PT)/deltaR_s = 1/2",
        "radial_density_coefficient_over_sin_theta": radial_coeff,
        "PT_joint_radial_coefficient_over_sin_theta": 0.0,
        "stress_slots_from_PT_pullback": pullback["stress_from_PT_pullback"],
        "scale_behavior": {
            "sqrt_q_kappa_l": "R_s/2",
            "d_dRs_sqrt_q_kappa_l": "1/2",
            "stress_mu": "4/R_s up to Barrabes-Israel convention",
            "stress_p": "-1/R_s up to Barrabes-Israel convention",
        },
        "closure": closure,
        "null_stationarity_selects_absolute_Rs": all(closure.values()),
        "obstruction": (
            "The reduced null/PT action has no internal length scale. Its radial "
            "variation is a constant in R_s, while the Barrabes-Israel stress slots "
            "scale as inverse powers of R_s. No finite absolute R_s is selected "
            "without an external mass/charge/state or additional action scale."
        ),
        "forbidden_shortcuts": [
            "do_not_set_Rs_to_one_as_physical_length",
            "do_not_treat_unit_Rs_as_absolute_scale",
            "do_not_choose_external_mass_by_observation_fit",
        ],
        "next_required": [
            "derive_external_mass_charge_or_state_for_Rs",
            "or_derive_new_action_scale_in_null_bridge_action",
        ],
        "gate_passed": True,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2 Null Sigma Stationarity Scale Obstruction Gate",
        "",
        payload["obstruction"],
        "",
        f"Stationarity selects absolute R_s: `{payload['null_stationarity_selects_absolute_Rs']}`",
        f"Equation: `{payload['stationarity_equation']}`",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
