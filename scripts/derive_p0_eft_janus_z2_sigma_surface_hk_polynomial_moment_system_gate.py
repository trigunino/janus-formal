from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.derive_p0_eft_janus_z2_sigma_surface_hk_polynomial_stress_tensor_gate import (
    build_payload as build_stress_tensor,
)


REPORT_PATH = Path(
    "outputs/reports/"
    "p0_eft_janus_z2_sigma_surface_hk_polynomial_moment_system_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/"
    "p0_eft_janus_z2_sigma_surface_hk_polynomial_moment_system_gate.json"
)


def build_payload() -> dict:
    stress = build_stress_tensor()
    density = {
        "L_Sigma": "a0 + a1*K + a2*K^2 + a3*K_ab*K^ab",
        "K_decomposition": "K_ab = K_tau u_a u_b + K_s q_ab",
        "trace": "K = -K_tau + 3*K_s",
    }
    bending_moment = {
        "D_ab": "a1*h_ab + 2*a2*K*h_ab + 2*a3*K_ab",
        "D_tau": "-a1 - 2*a2*K + 2*a3*K_tau",
        "D_s": "a1 + 2*a2*K + 2*a3*K_s",
        "alpha_K_radial": "sqrt_abs_h * (D_tau*dR_K_tau + 3*D_s*dR_K_s)",
    }
    coefficient_system = {
        "unknowns": ["a0", "a1", "a2", "a3"],
        "K_moment_equations_available": True,
        "metric_stress_equations_available": False,
        "a0_visible_in_D_ab": False,
        "a0_requires_metric_or_reference_energy_condition": True,
        "a1_a2_a3_solvable_from_D_only_if_three_independent_K_samples_exist": True,
    }
    return {
        "status": "janus-z2-sigma-surface-hk-polynomial-moment-system-gate",
        "active_core": "Z2_tunnel_Sigma",
        "source": "derived_from_surface_HK_variation_template",
        "density": density,
        "bending_moment": bending_moment,
        "coefficient_system": coefficient_system,
        "alpha_K_polynomial_moment_formula_ready": True,
        "alpha_h_surface_stress_formula_ready": stress["alpha_h_formula_ready"],
        "polynomial_stress_tensor_gate": {
            "status": stress["status"],
            "alpha_h_formula_ready": stress["alpha_h_formula_ready"],
            "alpha_K_formula_ready": stress["alpha_K_formula_ready"],
            "radial_contraction_formula_ready": stress["radial_contraction_formula_ready"],
        },
        "active_Janus_coefficients_derived": False,
        "gate_passed": False,
        "primary_blocker": "active_D_tau_D_s_or_surface_stress_targets",
        "next_required": [
            "derive_active_D_tau_and_D_s_or_R_K_trace_from_Sigma_boundary_residual",
            "derive_metric_surface_stress_T_surface_ab_for_alpha_h",
            "use_active_embedding_to_supply_K_tau_K_s_dR_K_tau_dR_K_s",
        ],
        "forbidden": [
            "do_not_solve_a_i_from_observational_BAO_or_CMB_data",
            "do_not_set_a0_by_hand",
            "do_not_claim_alpha_h_from_D_ab_only",
        ],
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# Janus Z2/Sigma Surface h/K Polynomial Moment System Gate",
        "",
        f"Gate passed: `{payload['gate_passed']}`",
        f"Primary blocker: `{payload['primary_blocker']}`",
        "",
        "## Bending Moment",
    ]
    lines.extend(f"- `{key}`: `{value}`" for key, value in payload["bending_moment"].items())
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    return "\n".join(lines)


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(render_markdown(payload), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
