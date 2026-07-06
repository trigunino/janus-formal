from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_souriau_boundary_moment_map_alpha_route.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_souriau_boundary_moment_map_alpha_route.json"
)


def build_payload() -> dict:
    return {
        "status": "janus-z2-sigma-souriau-boundary-moment-map-alpha-route",
        "active_core": "Z2_tunnel_Sigma",
        "source": "souriau_boundary_moment_map_audit",
        "souriau_phase_space_route_available": True,
        "boundary_moment_map_declared": True,
        "sigma_hamiltonian_boundary_functional_available": False,
        "moment_map_charge_conserved": True,
        "moment_map_variation_to_alpha_h_available": False,
        "moment_map_variation_to_alpha_K_available": False,
        "surface_hk_coefficients_written": False,
        "counterterm_trace_residual_inputs_written": False,
        "closes_E_counterterm": False,
        "closes_sigma_alpha_h": False,
        "negative_energy_orientation_supported": True,
        "negative_thermodynamic_density_postulated": False,
        "observational_fit_used": False,
        "archived_z4_reuse_used": False,
        "free_surface_density_added": False,
        "primary_blocker": "missing_sigma_hamiltonian_boundary_functional",
        "next_required": [
            "derive_boundary_Hamiltonian_H_Sigma_on_Souriau_orbit",
            "compute_delta_H_Sigma_over_delta_h_ab",
            "compute_delta_H_Sigma_over_delta_K_ab_if_extrinsic_dependence_exists",
            "only_then_write_sigma_alpha_h_inputs_or_counterterm_trace_residual_inputs",
        ],
        "verdict": (
            "Souriau supplies a clean charge/orbit framework and negative-sector "
            "orientation, but without an active boundary Hamiltonian on Sigma it "
            "does not produce alpha_h, alpha_K, or E_counterterm."
        ),
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Souriau Boundary Moment Map Alpha Route",
        "",
        f"Boundary moment map declared: `{payload['boundary_moment_map_declared']}`",
        f"Sigma Hamiltonian boundary functional available: `{payload['sigma_hamiltonian_boundary_functional_available']}`",
        f"Moment map charge conserved: `{payload['moment_map_charge_conserved']}`",
        f"alpha_h available: `{payload['moment_map_variation_to_alpha_h_available']}`",
        f"alpha_K available: `{payload['moment_map_variation_to_alpha_K_available']}`",
        f"Closes E_counterterm: `{payload['closes_E_counterterm']}`",
        f"Primary blocker: `{payload['primary_blocker']}`",
        "",
        f"Verdict: {payload['verdict']}",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
