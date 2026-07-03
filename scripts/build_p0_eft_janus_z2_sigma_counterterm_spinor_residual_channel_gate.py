from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_counterterm_spinor_residual_channel_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_counterterm_spinor_residual_channel_gate.json")


def build_payload() -> dict:
    declared = {
        "boundary_spinor_restriction_gate_declared": True,
        "spinor_boundary_projection_map_gate_declared": True,
        "spinor_bundle_projection_gate_declared": True,
        "projected_dirac_action_reduction_gate_declared": True,
        "dirac_boundary_variation_bibliography_checked": True,
        "spinor_variation_basis_declared": True,
        "projected_spinor_variation_transport_declared": True,
        "z2_pin_phase_policy_declared": True,
        "no_fitted_spinor_residual_coefficient": True,
    }
    closure = {
        "spinor_residual_coefficient_explicit": False,
        "conjugate_spinor_residual_coefficient_explicit": False,
        "spinor_residual_in_allowed_basis": False,
        "spinor_residual_compatible_with_projection": False,
        "spinor_residual_ready_for_one_form_decomposition": False,
    }
    return {
        "status": "janus-z2-sigma-counterterm-spinor-residual-channel-gate",
        "active_core": "Z2_tunnel_Sigma",
        "primary_sources_checked": [
            "Dirac action boundary variation",
            "MIT/projector-style boundary spinor variation",
            "active Sigma spinor projection gates",
        ],
        "bibliography_result": (
            "Dirac boundary variation supplies the spinor/conjugate-spinor channel. "
            "It does not compute the active Janus/Sigma projected coefficients R_psi."
        ),
        "declared": declared,
        "closure": closure,
        "channel_template": "alpha_psi = integral_Sigma (R_psi delta psi + delta psibar R_psibar)",
        "forbidden": [
            "fit spinor residual coefficient",
            "drop conjugate spinor channel",
            "bypass Sigma projection",
            "legacy Z4 spinor residual import",
        ],
        "counterterm_spinor_residual_channel_ledger_declared": all(declared.values()),
        "counterterm_spinor_residual_channel_ready": all(declared.values()) and all(closure.values()),
        "next_required": [
            "compute_R_psi_from_projected_dirac_boundary_variation",
            "compute_R_psibar_from_projected_dirac_boundary_variation",
            "prove_projection_compatibility_of_spinor_residual",
            "feed_R_psi_to_residual_one_form_decomposition_gate",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(
        "\n".join([
            "# Janus Z2/Sigma Counterterm Spinor Residual Channel Gate",
            "",
            f"Active core: `{payload['active_core']}`",
            f"Ledger declared: `{payload['counterterm_spinor_residual_channel_ledger_declared']}`",
            f"Channel ready: `{payload['counterterm_spinor_residual_channel_ready']}`",
            "",
            f"Template: `{payload['channel_template']}`",
        ]),
        encoding="utf-8",
    )
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
