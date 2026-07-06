from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path(
    "outputs/reports/"
    "p0_eft_janus_z2_sigma_hamiltonian_charge_to_friedmann_h0_map_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/"
    "p0_eft_janus_z2_sigma_hamiltonian_charge_to_friedmann_h0_map_gate.json"
)


def build_payload() -> dict:
    closure = {
        "friedmann_constraint_formula_declared": True,
        "charge_to_density_formula_declared": True,
        "SI_mass_energy_convention_declared": True,
        "boundary_charge_value_available": False,
        "boundary_charge_kind_fixed": False,
        "effective_volume_value_available": False,
        "curvature_radius_value_available": False,
        "absolute_RSigma_or_state_charge_available": False,
    }
    return {
        "status": "janus-z2-sigma-hamiltonian-charge-to-friedmann-h0-map-gate",
        "active_core": "Z2_tunnel_Sigma",
        "map": {
            "mass_charge_density": "rho_H = Q_boundary_kg / V_eff_m3",
            "energy_charge_density": "rho_H = E_boundary_J / (c^2 * V_eff_m3)",
            "friedmann_at_a1": (
                "H0_SI^2 = (8*pi*G_Z2Sigma/3) * rho_H "
                "- k_Z2Sigma*c^2/R_curv_Z2Sigma_m^2"
            ),
            "h0_km_s_mpc": "H0_km_s_Mpc = H0_SI * Mpc_m / 1000",
        },
        "dimension_check": {
            "Q_boundary_kg_over_V": "kg/m^3",
            "E_boundary_J_over_c2V": "kg/m^3",
            "8piG_rho_over_3": "1/s^2",
            "curvature_term": "1/s^2",
        },
        "closure": closure,
        "symbolic_map_ready": all(
            closure[key]
            for key in [
                "friedmann_constraint_formula_declared",
                "charge_to_density_formula_declared",
                "SI_mass_energy_convention_declared",
            ]
        ),
        "numeric_H0_ready": all(closure.values()),
        "blocked_by": [key for key, ok in closure.items() if not ok],
        "why_brown_york_energy_alone_is_insufficient": (
            "A boundary Hamiltonian charge is not a Hubble rate. It must first be "
            "converted to an effective mass density on the active FLRW volume, "
            "then inserted into the Friedmann constraint with the curvature term."
        ),
        "next_required": [
            "choose_or_derive_boundary_charge_kind_mass_or_energy",
            "derive_Q_boundary_or_E_boundary_from_RSigma_or_state_charge",
            "derive_effective_FLRW_volume_V_eff_m3",
            "derive_R_curv_Z2Sigma_m_or_flat_limit",
            "then_evaluate_H0_SI_and_write_background_H0_normalization_inputs_json",
        ],
        "gate_passed": True,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Hamiltonian Charge To Friedmann H0 Map Gate",
        "",
        payload["why_brown_york_energy_alone_is_insufficient"],
        "",
        f"Symbolic map ready: `{payload['symbolic_map_ready']}`",
        f"Numeric H0 ready: `{payload['numeric_H0_ready']}`",
        "",
        "## Map",
    ]
    lines.extend(f"- `{key}`: `{value}`" for key, value in payload["map"].items())
    lines.extend(["", "## Blocked By"])
    lines.extend(f"- `{item}`" for item in payload["blocked_by"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
