from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path(
    "outputs/reports/"
    "p0_eft_janus_z2_sigma_alpha_radial_coefficients_bibliography_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/"
    "p0_eft_janus_z2_sigma_alpha_radial_coefficients_bibliography_gate.json"
)


def build_payload() -> dict:
    sources = [
        {
            "key": "Armas_Tarrio_2017_surface_actions_DCFT",
            "url": "https://arxiv.org/pdf/1709.06766",
            "use": "surface_action_variation_with_induced_metric_and_extrinsic_curvature_sources",
            "closes_alpha_coefficients": False,
        },
        {
            "key": "PhysRevE_101_062803_membrane_EFT",
            "url": "https://pure.uva.nl/ws/files/54374675/PhysRevE.101.062803.pdf",
            "use": "explicit_bending_moment_for_L=a0+a1K+a2K2+a3KabKab",
            "closes_alpha_coefficients": False,
        },
        {
            "key": "Capovilla_Guven_1995",
            "url": "https://link.aps.org/doi/10.1103/PhysRevD.51.6736",
            "use": "normal_deformation_formulas_for_induced_metric_and_extrinsic_curvature",
            "closes_alpha_coefficients": False,
        },
        {
            "key": "Carter_2001_brane_dynamics",
            "url": "https://arxiv.org/abs/gr-qc/0012036",
            "use": "brane_force_balance_from_surface_stress_and_extrinsic_curvature",
            "closes_alpha_coefficients": False,
        },
        {
            "key": "Mars_Senovilla_2002",
            "url": "https://arxiv.org/abs/gr-qc/0201054",
            "use": "junction_and_distributional_Bianchi_consistency_for_general_hypersurfaces",
            "closes_alpha_coefficients": False,
        },
        {
            "key": "Lobo_Crawford_2005",
            "url": "https://arxiv.org/abs/gr-qc/0507063",
            "use": "thin_shell_radial_dynamics_and_momentum_flux_template",
            "closes_alpha_coefficients": False,
        },
        {
            "key": "Poisson_Visser_1995",
            "url": "https://arxiv.org/abs/gr-qc/9506083",
            "use": "throat_radius_to_extrinsic_curvature_jump_template",
            "closes_alpha_coefficients": False,
        },
        {
            "key": "blackfold_elastic_expansion",
            "url": "https://scispace.com/pdf/how-fluids-bend-the-elastic-expansion-for-higher-dimensional-57bty9e8pb.pdf",
            "use": "bending_moment_definition_as_functional_derivative_with_respect_to_K_ab",
            "closes_alpha_coefficients": False,
        },
        {
            "key": "boundary_higher_derivative_variational_principles",
            "url": "https://link.aps.org/doi/10.1103/PhysRevD.79.024028",
            "use": "warns_that_boundary_terms_fix_variational_principle_but_do_not_determine_model_specific_density",
            "closes_alpha_coefficients": False,
        },
    ]
    route = {
        "active_route": "geometric_surface_stress_plus_bending_moment",
        "variation_template": (
            "delta S_Sigma = integral sqrt_abs_h "
            "[-1/2 T_surface^ab delta h_ab + D^ab delta K_ab + ...]"
        ),
        "alpha_identification": {
            "alpha_h_ab": "-1/2 * T_surface^ab",
            "alpha_K_ab": "D^ab",
        },
        "surface_stress_definition": "R_h_ab := (1/sqrt_abs_h) delta S_ct / delta h^ab",
        "bending_moment_definition": "R_K_ab := (1/sqrt_abs_h) delta S_ct / delta K^ab",
        "polynomial_density_example": {
            "L_Sigma": "a0 + a1*K + a2*K^2 + a3*K_ab*K^ab",
            "D_ab": "a1*h_ab + 2*a2*K*h_ab + 2*a3*K_ab",
            "status": "template_only_until_active_Janus_coefficients_derived",
        },
        "radial_pullback": [
            "alpha_h_radial = sqrt_abs_h * R_h_ab * partial_R h^ab",
            "alpha_K_radial = sqrt_abs_h * R_K_ab * partial_R K^ab",
        ],
        "round_throat_trace_specialization": [
            "partial_R h_ab = 2 R_Sigma q_ab",
            "alpha_h_radial = sqrt_abs_h * 2 * R_Sigma * R_h_trace",
            "alpha_K_radial = sqrt_abs_h * R_K_trace",
        ],
    }
    return {
        "status": "janus-z2-sigma-alpha-radial-coefficients-bibliography-gate",
        "active_core": "Z2_tunnel_Sigma",
        "bibliography_checked": True,
        "sources": sources,
        "route": route,
        "bibliography_closes_alpha_h_alpha_K": False,
        "bibliography_selects_route": True,
        "best_next_step": "instantiate_surface_HK_variation_template_with_active_Janus_Sigma_density",
        "forbidden": [
            "do_not_import_generic_thin_shell_coefficients_as_Janus_counterterm",
            "do_not_reuse_Cartan_GHY_linear_K_trace_as_non_GHY_residual",
            "do_not_fit_alpha_h_or_alpha_K_from_observations",
        ],
        "gate_passed": False,
        "primary_blocker": "active_Janus_Sigma_density_or_surface_stress_bending_moment_values",
        "next_required": [
            "derive_or_emit_R_h_ab_surface_stress_from_active_S_ct",
            "derive_or_emit_R_K_ab_bending_moment_from_active_S_ct",
            "contract_with_partial_R_h_ab_and_partial_R_K_ab_on_Sigma",
        ],
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# Janus Z2/Sigma Alpha Radial Coefficients Bibliography Gate",
        "",
        f"Gate passed: `{payload['gate_passed']}`",
        f"Primary blocker: `{payload['primary_blocker']}`",
        f"Route selected: `{payload['route']['active_route']}`",
        "",
        "## Sources",
    ]
    lines.extend(f"- `{src['key']}`: {src['url']}" for src in payload["sources"])
    lines.extend(["", "## Radial Pullback"])
    lines.extend(f"- `{item}`" for item in payload["route"]["radial_pullback"])
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
