from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z2_sigma_reflecting_spinor_boundary_current_gate import (
    build_payload as build_reflecting_current_payload,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_counterterm_spinor_residual_channel_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_counterterm_spinor_residual_channel_gate.json")


def build_payload() -> dict:
    reflecting = build_reflecting_current_payload()
    local_reflecting_zero_ready = bool(reflecting["local_normal_dirac_current_zero_ready"])
    local_projection_ready = bool(
        reflecting["upstream_frontiers"]["spinor_boundary_projection"]["closure"][
            "local_Z2Sigma_spinor_projection_ready"
        ]
    )
    local_projected_residual_zero_ready = local_reflecting_zero_ready and local_projection_ready
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
        "spinor_residual_coefficient_explicit": local_projected_residual_zero_ready,
        "conjugate_spinor_residual_coefficient_explicit": local_projected_residual_zero_ready,
        "spinor_residual_in_allowed_basis": local_projected_residual_zero_ready,
        "spinor_residual_compatible_with_projection": local_projected_residual_zero_ready,
        "spinor_residual_ready_for_one_form_decomposition": local_projected_residual_zero_ready,
    }
    conditional_reflecting_projector = {
        "local_MIT_reflecting_projector_ready": bool(
            reflecting["closure"]["local_MIT_current_zero_algebra_ready"]
        ),
        "normal_current_zero_algebra_ready": bool(
            reflecting["closure"]["local_MIT_current_zero_algebra_ready"]
        ),
        "boundary_spinor_satisfies_projector_derived": bool(
            reflecting["closure"]["local_reflecting_boundary_condition_derived"]
        ),
        "spinor_residual_zero_if_reflecting_projector_imposed": local_reflecting_zero_ready,
        "conditional_only_not_physical_boundary_condition": False,
        "global_Z2Sigma_spinor_projection_ready": bool(
            reflecting["closure"]["spinor_boundary_projection_map_ready"]
        ),
        "local_projected_spinor_residual_zero_ready": local_projected_residual_zero_ready,
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
        "conditional_reflecting_projector_route": conditional_reflecting_projector,
        "upstream_frontiers": {
            "reflecting_spinor_boundary_current": {
                "gate": reflecting["status"],
                "local_ready": reflecting["local_normal_dirac_current_zero_ready"],
                "global_ready": reflecting["normal_dirac_current_zero_ready"],
                "primary_blocker": reflecting["primary_blocker"],
                "closure": reflecting["closure"],
            }
        },
        "channel_template": "alpha_psi = integral_Sigma (R_psi delta psi + delta psibar R_psibar)",
        "conditional_formula": (
            "If psi=P_reflect psi and delta psi=P_reflect delta psi on Sigma, "
            "then the local MIT algebra gives the normal-current boundary bilinear "
            "zero; the local reflecting condition is derived, while the global "
            "Z2Sigma spinor projection remains open."
        ),
        "projected_residual_coefficients": {
            "scope": "local_Sigma_reflecting_projected_variation",
            "R_psi": "0",
            "R_psibar": "0",
            "global_resolved_tunnel_spinor_bundle_claimed": False,
        },
        "forbidden": [
            "fit spinor residual coefficient",
            "drop conjugate spinor channel",
            "bypass Sigma projection",
            "legacy Z4 spinor residual import",
            "promote conditional MIT algebra as physical boundary condition",
        ],
        "counterterm_spinor_residual_channel_ledger_declared": all(declared.values()),
        "counterterm_spinor_residual_channel_ready": all(declared.values()) and all(closure.values()),
        "primary_blocker": (
            "none"
            if all(declared.values()) and all(closure.values())
            else "projected_spinor_residual_coefficients"
            if local_projection_ready
            else "reflecting_spinor_boundary_current"
        ),
        "next_required": [
            "close_global_Z2Sigma_spinor_projection_map",
            "keep_local_spinor_residual_zero_in_residual_one_form_decomposition",
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
            f"Primary blocker: `{payload['primary_blocker']}`",
            "",
            f"Template: `{payload['channel_template']}`",
            f"Conditional route: `{payload['conditional_formula']}`",
        ]),
        encoding="utf-8",
    )
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
