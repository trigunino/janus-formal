from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_counterterm_matter_flux_residual_channel_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_counterterm_matter_flux_residual_channel_gate.json")


def build_payload() -> dict:
    declared = {
        "matter_flux_radial_block_gate_declared": True,
        "matter_flux_active_projection_gate_declared": True,
        "bulk_stress_of_a_gate_declared": True,
        "bulk_stress_normal_flux_cancellation_gate_declared": True,
        "matter_flux_boundary_variation_bibliography_checked": True,
        "normal_tangent_flux_formula_declared": True,
        "z2_flux_orientation_declared": True,
        "active_flux_of_a_declared": True,
        "no_fitted_matter_residual_coefficient": True,
    }
    closure = {
        "matter_residual_coefficient_explicit": False,
        "matter_residual_in_allowed_basis": False,
        "matter_residual_ready_for_one_form_decomposition": False,
    }
    return {
        "status": "janus-z2-sigma-counterterm-matter-flux-residual-channel-gate",
        "active_core": "Z2_tunnel_Sigma",
        "primary_sources_checked": [
            "stress-energy flux through hypersurface",
            "thin-shell matter flux balance",
            "active bulk-stress and matter-flux gates",
        ],
        "bibliography_result": (
            "Flux-balance literature identifies the matter residual channel, but the "
            "active Janus/Sigma projected matter coefficient R_matter is not computed."
        ),
        "declared": declared,
        "closure": closure,
        "channel_template": "alpha_matter = integral_Sigma R_matter delta matter",
        "forbidden": [
            "fit matter residual coefficient",
            "assume transparency without active projection",
            "drop matter flux channel",
            "legacy Z4 matter residual import",
        ],
        "counterterm_matter_flux_residual_channel_ledger_declared": all(declared.values()),
        "counterterm_matter_flux_residual_channel_ready": all(declared.values()) and all(closure.values()),
        "next_required": [
            "compute_R_matter_from_active_normal_flux_variation",
            "derive_active_flux_of_a",
            "express_R_matter_in_allowed_local_density_basis",
            "feed_R_matter_to_residual_one_form_decomposition_gate",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(
        "\n".join([
            "# Janus Z2/Sigma Counterterm Matter-Flux Residual Channel Gate",
            "",
            f"Active core: `{payload['active_core']}`",
            f"Ledger declared: `{payload['counterterm_matter_flux_residual_channel_ledger_declared']}`",
            f"Channel ready: `{payload['counterterm_matter_flux_residual_channel_ready']}`",
        ]),
        encoding="utf-8",
    )
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
