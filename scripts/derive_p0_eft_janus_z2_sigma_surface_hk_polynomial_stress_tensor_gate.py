from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path(
    "outputs/reports/"
    "p0_eft_janus_z2_sigma_surface_hk_polynomial_stress_tensor_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/"
    "p0_eft_janus_z2_sigma_surface_hk_polynomial_stress_tensor_gate.json"
)


def build_payload() -> dict:
    density = {
        "L_Sigma": "a0 + a1*K + a2*K^2 + a3*K_ab*K^ab",
        "K": "h^ab*K_ab",
        "K_abKab": "K_ab*K_cd*h^ac*h^bd",
        "variation_policy": "vary h_ab and K_ab independently",
    }
    alpha = {
        "alpha_K_ab": "a1*h^ab + 2*a2*K*h^ab + 2*a3*K^ab",
        "alpha_h_ab": (
            "1/2*h^ab*L_Sigma - (a1 + 2*a2*K)*K^ab "
            "- 2*a3*K^a_c*K^bc"
        ),
        "surface_stress": "T_surface^ab = -2*alpha_h_ab",
        "radial_alpha": (
            "alpha_R = sqrt_abs_h*(alpha_h_ab*partial_R_h_ab "
            "+ alpha_K_ab*partial_R_K_ab)"
        ),
    }
    derivation = {
        "delta_sqrt_abs_h": "1/2*sqrt_abs_h*h^ab*delta_h_ab",
        "delta_h_inverse": "delta h^ab = -h^ac*h^bd*delta_h_cd",
        "delta_K_fixed_Kab": "-K^ab*delta_h_ab",
        "delta_KabKab_fixed_Kab": "-2*K^a_c*K^bc*delta_h_ab",
    }
    return {
        "status": "janus-z2-sigma-surface-hk-polynomial-stress-tensor-gate",
        "active_core": "Z2_tunnel_Sigma",
        "source": "direct_variation_of_polynomial_surface_density",
        "density": density,
        "derivation": derivation,
        "alpha_coefficients": alpha,
        "alpha_h_formula_ready": True,
        "alpha_K_formula_ready": True,
        "radial_contraction_formula_ready": True,
        "active_Janus_coefficients_ready": False,
        "active_embedding_radial_derivatives_ready": False,
        "gate_passed": False,
        "primary_blocker": "active_a_i_coefficients_and_radial_embedding_derivatives",
        "next_required": [
            "derive_active_a0_a1_a2_a3_or_replace_polynomial_by_active_density",
            "provide_partial_R_h_ab_on_Sigma",
            "provide_partial_R_K_ab_on_Sigma",
            "evaluate_alpha_R_on_active_a_grid",
        ],
        "forbidden": [
            "do_not_fit_a_i_to_observations",
            "do_not_set_partial_R_K_ab_to_zero_without_embedding_derivation",
            "do_not_claim_polynomial_template_is_the_active_Janus_density",
        ],
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# Janus Z2/Sigma Surface h/K Polynomial Stress Tensor Gate",
        "",
        f"Gate passed: `{payload['gate_passed']}`",
        f"Primary blocker: `{payload['primary_blocker']}`",
        "",
        "## Alpha Coefficients",
    ]
    lines.extend(f"- `{key}`: `{value}`" for key, value in payload["alpha_coefficients"].items())
    lines.extend(["", "## Derivation"])
    lines.extend(f"- `{key}`: `{value}`" for key, value in payload["derivation"].items())
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
