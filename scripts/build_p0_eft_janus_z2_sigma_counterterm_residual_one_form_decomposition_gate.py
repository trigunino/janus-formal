from __future__ import annotations

import json
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from scripts.build_p0_eft_janus_z2_sigma_counterterm_residual_channel_frontier_gate import (
    build_payload as build_channel_frontier_payload,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_counterterm_residual_one_form_decomposition_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_counterterm_residual_one_form_decomposition_gate.json")


def build_payload() -> dict:
    channel_frontier = build_channel_frontier_payload()
    declared = {
        "nonlinear_residual_closure_imported": True,
        "local_density_basis_gate_declared": True,
        "variational_bicomplex_bibliography_checked": True,
        "residual_one_form_problem_declared": True,
        "active_field_coordinates_declared": True,
        "tetrad_residual_channel_gate_declared": True,
        "connection_residual_channel_gate_declared": True,
        "spinor_residual_channel_gate_declared": True,
        "embedding_residual_channel_gate_declared": True,
        "matter_flux_residual_channel_gate_declared": True,
        "tetrad_residual_channel_declared": True,
        "connection_residual_channel_declared": True,
        "spinor_residual_channel_declared": True,
        "embedding_residual_channel_declared": True,
        "matter_flux_residual_channel_declared": True,
        "no_fitted_residual_coefficient": True,
    }
    closure = {
        "residual_one_form_components_explicit": channel_frontier["channels"][
            "all_residual_channels_explicit"
        ],
        "residual_one_form_local_in_allowed_basis": channel_frontier["channels"][
            "residual_one_form_ready_for_decomposition"
        ],
        "residual_one_form_ready_for_integrability_gate": channel_frontier["channels"][
            "residual_one_form_ready_for_decomposition"
        ],
    }
    ready = all(declared.values()) and all(closure.values())
    primary_blocker = (
        "none"
        if ready
        else channel_frontier.get("primary_blocker", "counterterm_residual_channels")
    )
    residual_channels = channel_frontier["channels"]
    next_required = []
    if not residual_channels["tetrad_residual_ready"]:
        next_required.extend(
            [
                "compute_tetrad_residual_channel",
                "pass_counterterm_tetrad_residual_channel_gate",
            ]
        )
    if not residual_channels["connection_residual_ready"]:
        next_required.extend(
            [
                "compute_connection_residual_channel",
                "pass_counterterm_connection_residual_channel_gate",
            ]
        )
    if not residual_channels["spinor_residual_ready"]:
        next_required.extend(
            [
                "compute_spinor_residual_channel",
                "pass_counterterm_spinor_residual_channel_gate",
            ]
        )
    if not residual_channels["embedding_residual_ready"]:
        next_required.extend(
            [
                "compute_embedding_residual_channel",
                "pass_counterterm_embedding_residual_channel_gate",
            ]
        )
    if not residual_channels["matter_flux_residual_ready"]:
        next_required.extend(
            [
                "compute_matter_flux_residual_channel",
                "pass_counterterm_matter_flux_residual_channel_gate",
            ]
        )
    next_required.extend(
        [
            "express_residual_channels_in_allowed_basis",
            "feed_one_form_to_integrability_gate",
        ]
    )

    return {
        "status": "janus-z2-sigma-counterterm-residual-one-form-decomposition-gate",
        "active_core": "Z2_tunnel_Sigma",
        "primary_sources_checked": [
            "active Sigma nonlinear residual closure gate",
            "active Sigma counterterm local density basis gate",
            "active tetrad residual channel gate",
            "active connection residual channel gate",
            "active spinor residual channel gate",
            "active embedding residual channel gate",
            "active matter-flux residual channel gate",
            "Hamilton-Jacobi boundary counterterm method",
            "covariant phase space / variational bicomplex with boundary",
        ],
        "bibliography_result": (
            "Primary methods support treating the boundary residual as a field-space "
            "one-form and testing exactness before integrating a counterterm. They do "
            "not supply the active Janus/Sigma channel coefficients."
        ),
        "declared": declared,
        "closure": closure,
        "upstream_frontiers": {
            "residual_channels": {
                "gate": channel_frontier["status"],
                "ready": channel_frontier["residual_channel_frontier_ready"],
                "channels": channel_frontier["channels"],
                "channel_frontiers": channel_frontier["channel_frontiers"],
                "current_frontier": channel_frontier["current_frontier"],
                "primary_blocker": channel_frontier.get("primary_blocker", "counterterm_residual_channels"),
            },
        },
        "one_form_template": (
            "alpha_res = R_e delta e + R_omega delta omega + R_psi delta psi "
            "+ R_X delta X + R_matter delta matter"
        ),
        "allowed_basis": [
            "h_ab",
            "K_ab",
            "Sigma torsion pullback",
            "Immirzi/radion boundary fields",
            "Z2 orientation sign",
        ],
        "forbidden": [
            "fit residual coefficient",
            "manual channel suppression",
            "legacy Z4 residual import",
        ],
        "counterterm_residual_one_form_decomposition_ledger_declared": all(declared.values()),
        "counterterm_residual_one_form_decomposition_ready": ready,
        "gate_passed": ready,
        "primary_blocker": primary_blocker,
        "next_required": next_required,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Counterterm Residual One-Form Decomposition Gate",
        "",
        f"Active core: `{payload['active_core']}`",
        f"Ledger declared: `{payload['counterterm_residual_one_form_decomposition_ledger_declared']}`",
        f"Ready: `{payload['counterterm_residual_one_form_decomposition_ready']}`",
        "",
        "## One-Form Template",
        f"`{payload['one_form_template']}`",
        "",
        "## Next Required",
    ]
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
