from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_chi_ll_spectral_bridge_matrix.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_chi_ll_spectral_bridge_matrix.json")


def build_payload() -> dict:
    bridges = {
        "Casimir_topological_exit": {
            "spectral_help": [
                "supplies mode scale lambda ~ 1/R_s or 1/R_s^2",
                "supports rho_Casimir ~ C/R_s^4",
                "shares operator/field-content data with Casimir coefficient C",
            ],
            "newly_calculable": ["power_law_Rs_dependence"],
            "still_blocked_by": [
                "field_content",
                "boundary_conditions",
                "renormalized_C",
                "R_s_selection_or_stationarity",
            ],
            "unblocked": False,
        },
        "spin_condensate_exit": {
            "spectral_help": [
                "Dirac spectrum gives fermion levels on Sigma",
                "can define density of states and Fermi filling once occupation is known",
                "connects naturally to axial current and Holst/Cartan torsion",
            ],
            "newly_calculable": ["level_spacing_scale_1_over_Rs"],
            "still_blocked_by": [
                "fermion_occupation_or_state",
                "spin_polarization",
                "mass_or_chemical_potential_law",
                "projection_to_torsion_stress",
            ],
            "unblocked": False,
        },
        "horizon_thermodynamic_exit": {
            "spectral_help": [
                "same dimension as surface gravity kappa_l ~ 1/R_s",
                "can compare spectral gap to Hawking temperature scale",
                "helps test if horizon normalization is geometrically natural",
            ],
            "newly_calculable": ["temperature_scale_if_kappa_l_equals_c_over_Rs_convention"],
            "still_blocked_by": [
                "proof_Sigma_PT_is_horizon",
                "surface_gravity_normalization",
                "first_law_energy_definition",
                "R_s_selection",
            ],
            "unblocked": False,
        },
        "area_gap_exit": {
            "spectral_help": [
                "if A_Sigma=N*A_gap then R_s is fixed and spectral gaps follow",
                "spectral data can become a consistency check of the area-gap route",
            ],
            "newly_calculable": ["spectral_gap_after_area_gap"],
            "still_blocked_by": [
                "quantum_area_operator_on_Sigma",
                "A_Sigma_equals_N_gap_A_gap_theorem",
                "integer_N_gap_selection",
            ],
            "unblocked": False,
        },
        "UV_LL_action_exit": {
            "spectral_help": [
                "brane modes can renormalize or induce lambda_F2/F2_0",
                "operator data can supply allowed boundary conditions for LL fields",
            ],
            "newly_calculable": ["none_without_quantum_LL_action"],
            "still_blocked_by": [
                "microscopic_LL_quantum_action",
                "q_LL_normalization",
                "lambda_F2_or_F2_0_derivation",
                "physical_area_gauge",
            ],
            "unblocked": False,
        },
    }
    return {
        "status": "janus-z2-chi-ll-spectral-bridge-matrix",
        "active_core": "Z2_tunnel_Sigma_null_PT_bridge",
        "purpose": "propagate the 1/R_s spectral scale into the remaining chi_LL exit routes",
        "global_result": (
            "The spectral scale is a connector, not a selector. It turns several "
            "routes into functions of R_s, but it does not choose R_s without "
            "an independent area, state, horizon, action, or stationarity law."
        ),
        "bridges": bridges,
        "routes_unblocked_by_spectral_scale_alone": [
            name for name, data in bridges.items() if data["unblocked"]
        ],
        "best_combined_routes": [
            "area_gap_exit -> spectral_gap -> Casimir coefficient consistency",
            "spectral_Dirac_levels -> spin_condensate_exit",
            "horizon_kappa_l ~ 1/R_s -> thermodynamic consistency check",
            "quantum_LL_action -> spectral boundary modes -> lambda_F2/F2_0",
        ],
        "chi_LL_prediction_ready": False,
        "gate_passed": True,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2 chi_LL Spectral Bridge Matrix",
        "",
        payload["global_result"],
        "",
        f"chi_LL prediction ready: `{payload['chi_LL_prediction_ready']}`",
        "",
        "## Bridges",
    ]
    for name, data in payload["bridges"].items():
        lines.append(f"- `{name}`: unblocked=`{data['unblocked']}`")
    lines.extend(["", "## Best Combined Routes"])
    lines.extend(f"- {item}" for item in payload["best_combined_routes"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
