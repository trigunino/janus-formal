from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z2_sigma_surface_hk_variation_convention_gate import (
    build_payload as build_conventions,
)


REPORT_PATH = Path(
    "outputs/reports/"
    "p0_eft_janus_z2_sigma_surface_hk_variation_alpha_coefficient_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/"
    "p0_eft_janus_z2_sigma_surface_hk_variation_alpha_coefficient_gate.json"
)


def build_payload() -> dict:
    conventions = build_conventions()
    template = {
        "variation": (
            "delta S_Sigma = integral_Sigma sqrt_abs_h "
            "[-1/2 T_surface^ab delta h_ab + D^ab delta K_ab + ...]"
        ),
        "alpha_h_ab": "-1/2 * T_surface^ab",
        "alpha_K_ab": "D^ab",
        "radial_contraction": (
            "alpha_R = sqrt_abs_h * (alpha_h^ab partial_R h_ab "
            "+ alpha_K^ab partial_R K_ab)"
        ),
    }
    polynomial_density = {
        "L_Sigma": "a0 + a1*K + a2*K^2 + a3*K_ab*K^ab",
        "D_ab": "a1*h_ab + 2*a2*K*h_ab + 2*a3*K_ab",
        "coefficient_status": "template_only_not_active_Janus_values",
    }
    convention_guards = {
        "K_ab_sign_convention_declared": conventions["guards"][
            "K_ab_sign_convention_declared"
        ],
        "normal_orientation_declared": conventions["guards"]["normal_orientation_declared"],
        "metric_variation_index_position_declared": conventions["guards"][
            "metric_variation_index_position_declared"
        ],
        "signature_convention_declared": conventions["guards"]["signature_convention_declared"],
    }
    return {
        "status": "janus-z2-sigma-surface-hk-variation-alpha-coefficient-gate",
        "active_core": "Z2_tunnel_Sigma",
        "source": "bibliography_supported_variational_template",
        "primary_reference": "Armas_Tarrio_2017_surface_actions_DCFT",
        "secondary_reference": "PhysRevE_101_062803_membrane_EFT",
        "template": template,
        "polynomial_density_example": polynomial_density,
        "surface_HK_variation_template_ready": True,
        "alpha_identification_ready": True,
        "active_Janus_coefficients_derived": False,
        "active_R_h_ab_ready": False,
        "active_R_K_ab_ready": False,
        "convention_guards": convention_guards,
        "convention_gate": {
            "status": conventions["status"],
            "ready": conventions["conventions_ready"],
            "active_delta_K_value_transport_ready": conventions[
                "active_delta_K_value_transport_ready"
            ],
        },
        "conventions_ready": all(convention_guards.values()),
        "gate_passed": False,
        "primary_blocker": (
            "active_Janus_Sigma_density_coefficients"
            if all(convention_guards.values())
            else "active_Janus_Sigma_density_coefficients_and_conventions"
        ),
        "next_required": (
            [
                "derive_active_Janus_coefficients_a0_a1_a2_a3_or_nonpolynomial_density",
                "compute_T_surface_ab_from_active_density",
                "compute_D_ab_from_active_density",
                "contract_with_partial_R_h_ab_and_partial_R_K_ab",
            ]
            if all(convention_guards.values())
            else [
                "fix_K_ab_sign_normal_orientation_signature_and_index_conventions",
                "derive_active_Janus_coefficients_a0_a1_a2_a3_or_nonpolynomial_density",
                "compute_T_surface_ab_from_active_density",
                "compute_D_ab_from_active_density",
                "contract_with_partial_R_h_ab_and_partial_R_K_ab",
            ]
        ),
        "forbidden": [
            "do_not_choose_a0_a1_a2_a3_by_fit",
            "do_not_treat_template_density_as_active_Janus_derivation",
            "do_not_ignore_K_ab_sign_and_normal_orientation",
        ],
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# Janus Z2/Sigma Surface h/K Variation Alpha Coefficient Gate",
        "",
        f"Gate passed: `{payload['gate_passed']}`",
        f"Primary blocker: `{payload['primary_blocker']}`",
        f"Template ready: `{payload['surface_HK_variation_template_ready']}`",
        "",
        "## Template",
        f"`{payload['template']['variation']}`",
        f"`alpha_h_ab = {payload['template']['alpha_h_ab']}`",
        f"`alpha_K_ab = {payload['template']['alpha_K_ab']}`",
        "",
        "## Polynomial Example",
        f"`{payload['polynomial_density_example']['L_Sigma']}`",
        f"`D_ab = {payload['polynomial_density_example']['D_ab']}`",
        "",
        "## Next Required",
    ]
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
