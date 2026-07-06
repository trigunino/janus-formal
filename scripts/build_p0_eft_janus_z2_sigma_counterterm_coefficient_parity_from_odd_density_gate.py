from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.derive_p0_eft_janus_z2_sigma_counterterm_variational_coefficient_formula import (
    build_payload as build_variational_formula,
)
from scripts.build_p0_eft_janus_z2_sigma_counterterm_tetrad_component_parity_gate import (
    build_payload as build_tetrad_parity,
)
from scripts.build_p0_eft_janus_z2_sigma_counterterm_lct_z2_odd_density_gate import (
    build_payload as build_lct_odd_density,
)


REPORT_PATH = Path(
    "outputs/reports/"
    "p0_eft_janus_z2_sigma_counterterm_coefficient_parity_from_odd_density_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/"
    "p0_eft_janus_z2_sigma_counterterm_coefficient_parity_from_odd_density_gate.json"
)


def build_payload() -> dict:
    formula = build_variational_formula()
    tetrad = build_tetrad_parity()
    lct_odd = build_lct_odd_density()
    lct_z2_odd_proved = lct_odd["closure"]["L_ct_Z2_odd_density_proved"]
    conditional_derivation_ready = bool(
        formula["formula_derivation_closed"]
        and tetrad["closure"]["metric_variation_parity_ready"]
        and tetrad["closure"]["extrinsic_variation_parity_ready"]
    )
    rh_parity_proved = conditional_derivation_ready and lct_z2_odd_proved
    rk_parity_proved = conditional_derivation_ready and lct_z2_odd_proved
    gate_passed = rh_parity_proved and rk_parity_proved
    return {
        "status": "janus-z2-sigma-counterterm-coefficient-parity-from-odd-density-gate",
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "declared": {
            "variational_coefficient_formula_imported": formula["formula_derivation_closed"],
            "h_even_K_odd_parity_imported": conditional_derivation_ready,
            "odd_density_route_declared": True,
            "no_density_ansatz_used": True,
            "fitted_coefficient_forbidden": True,
            "legacy_z4_reuse_forbidden": True,
        },
        "formulae": {
            "R_h_ab": formula["formulas"]["R_h_ab"],
            "R_K_ab": formula["formulas"]["R_K_ab"],
            "density_parity_assumption": "tau_Z2^* L_ct(h,K,...) = -L_ct(h,K,...)",
            "metric_derivative_parity": "h even and L_ct odd -> partial L_ct / partial h_ab is odd",
            "extrinsic_derivative_parity": "K odd and L_ct odd -> partial L_ct / partial K_ab is even",
            "result_R_h": "tau_Z2^* R_h_ab = -R_h_ab",
            "result_R_K": "tau_Z2^* R_K_ab = +R_K_ab",
        },
        "conditional_derivation": {
            "if_L_ct_Z2_odd_then_R_h_ab_Z2_odd": conditional_derivation_ready,
            "if_L_ct_Z2_odd_then_R_K_ab_Z2_even": conditional_derivation_ready,
            "proof_scope": "parity_only_not_values",
        },
        "closure": {
            "L_ct_Z2_odd_density_proved": lct_z2_odd_proved,
            "R_h_ab_Z2_odd_coefficient_parity_proved": rh_parity_proved,
            "R_K_ab_Z2_even_coefficient_parity_proved": rk_parity_proved,
            "coefficient_parity_gate_passed": gate_passed,
        },
        "upstream_frontiers": {
            "L_ct_Z2_odd_density": {
                "gate": lct_odd["status"],
                "ready": lct_odd["closure"]["L_ct_Z2_odd_density_proved"],
                "primary_blocker": lct_odd["primary_blocker"],
            }
        },
        "gate_passed": gate_passed,
        "primary_blocker": "L_ct_Z2_odd_density" if not gate_passed else "none",
        "interpretation": (
            "The requested coefficient parities are derivable from the existing "
            "variation formula if the Sigma counterterm density is Z2-odd. That "
            "oddness is not yet proved, so this closes only the conditional algebra."
        ),
        "next_required": []
        if gate_passed
        else [
            "prove_tau_Z2_pullback_L_ct_equals_minus_L_ct",
            "or_emit_alpha_res_component_values_then_integrate_L_ct_primitive_and_check_parity",
            "or_return_to_nonzero_E_counterterm_radial_route",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Counterterm Coefficient Parity From Odd Density Gate",
        "",
        f"Gate passed: `{payload['gate_passed']}`",
        f"Primary blocker: `{payload['primary_blocker']}`",
        "",
        payload["interpretation"],
        "",
        "## Formulae",
    ]
    lines.extend(f"- `{key}`: `{value}`" for key, value in payload["formulae"].items())
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
