from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_souriau_boundary_hamiltonian_attempt.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_souriau_boundary_hamiltonian_attempt.json"
)


def build_payload() -> dict:
    return {
        "status": "janus-z2-sigma-souriau-boundary-hamiltonian-attempt",
        "active_core": "Z2_tunnel_Sigma",
        "source": "souriau_boundary_hamiltonian_derivation_attempt",
        "moment_map_charge_Q_sigma_declared": True,
        "deck_invariant_charge_reduction": "Q_Sigma = N_occ",
        "absolute_occupation_fixed": False,
        "boundary_hamiltonian_candidate": "H_Sigma = mu_Sigma * Q_Sigma",
        "mu_Sigma_available_from_existing_geometry": False,
        "local_density_from_charge_available": False,
        "metric_variation_available": False,
        "extrinsic_curvature_variation_available": False,
        "alpha_h_from_souriau_hamiltonian": False,
        "alpha_K_from_souriau_hamiltonian": False,
        "counterterm_trace_residual_inputs_written": False,
        "surface_hk_coefficients_written": False,
        "closes_E_counterterm": False,
        "primary_blocker": "moment_map_gives_global_charge_not_local_boundary_density",
        "not_a_rustine": True,
        "requires_new_physical_input": [
            "chemical_potential_or_energy_per_projected_charge_mu_Sigma",
            "or local Souriau-KKS boundary symplectic potential density on Sigma",
            "or active matter Hamiltonian density coupled to h_ab/K_ab",
        ],
        "forbidden_shortcuts": [
            "set_mu_Sigma_by_observation",
            "identify_Q_Sigma_with_density_without_volume_or_state",
            "differentiate_global_charge_as_if_it_were_local_surface_action",
        ],
        "verdict": (
            "The Souriau moment map gives a clean global charge/Hamiltonian label. "
            "Without an energy-per-charge or KKS boundary density on Sigma, "
            "H_Sigma has no active local h_ab or K_ab variation, so alpha_h and "
            "alpha_K remain unavailable."
        ),
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(
        "\n".join(
            [
                "# Janus Z2/Sigma Souriau Boundary Hamiltonian Attempt",
                "",
                f"Charge reduction: `{payload['deck_invariant_charge_reduction']}`",
                f"Boundary Hamiltonian candidate: `{payload['boundary_hamiltonian_candidate']}`",
                f"Local density available: `{payload['local_density_from_charge_available']}`",
                f"alpha_h available: `{payload['alpha_h_from_souriau_hamiltonian']}`",
                f"alpha_K available: `{payload['alpha_K_from_souriau_hamiltonian']}`",
                f"Closes E_counterterm: `{payload['closes_E_counterterm']}`",
                f"Primary blocker: `{payload['primary_blocker']}`",
                "",
                f"Verdict: {payload['verdict']}",
            ]
        ),
        encoding="utf-8",
    )
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
