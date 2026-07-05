from __future__ import annotations

import json
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from scripts.build_p0_eft_janus_z2_sigma_counterterm_tetrad_variation_transport_readiness_gate import (
    build_payload as build_tetrad_transport_readiness_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_counterterm_local_density_basis_gate import (
    build_payload as build_local_density_basis_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_counterterm_tetrad_metric_residual_coefficient_input_writer_gate import (
    build_payload as build_metric_coefficient_writer_payload,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_counterterm_tetrad_residual_channel_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_counterterm_tetrad_residual_channel_gate.json")


def build_payload() -> dict:
    transport_readiness = build_tetrad_transport_readiness_payload()
    local_basis = build_local_density_basis_payload()
    metric_coefficient_writer = build_metric_coefficient_writer_payload()
    declared = {
        "coframe_connection_pullback_gate_declared": True,
        "residual_one_form_decomposition_gate_declared": True,
        "palatini_holst_tetrad_variation_bibliography_checked": True,
        "tetrad_residual_channel_problem_declared": True,
        "coframe_variation_basis_declared": True,
        "induced_metric_variation_transport_declared": True,
        "extrinsic_curvature_variation_transport_declared": True,
        "torsion_pullback_variation_transport_declared": True,
        "z2_orientation_variation_policy_declared": True,
        "no_fitted_tetrad_residual_coefficient": True,
    }
    transport_ready = transport_readiness["tetrad_variation_readiness_ready"]
    metric_subchannel_ready = transport_readiness["readiness"][
        "induced_metric_variation_transport_ready"
    ]
    boundary_residual_formula_ready = False
    residual_ready = transport_ready and boundary_residual_formula_ready
    basis_ready = (
        local_basis["closure"]["unique_counterterm_transported"]
        and local_basis["closure"]["local_density_basis_complete"]
    )
    closure = {
        "tetrad_metric_residual_subchannel_explicit": metric_subchannel_ready,
        "tetrad_metric_residual_coefficient_formula_declared": metric_subchannel_ready,
        "tetrad_metric_residual_coefficient_value_ready": metric_coefficient_writer[
            "tetrad_metric_residual_coefficient_value_ready"
        ],
        "tetrad_variation_transport_ready": transport_ready,
        "allowed_local_density_basis_ready": basis_ready,
        "active_sigma_boundary_variation_residual_formula_ready": boundary_residual_formula_ready,
        "tetrad_residual_coefficient_explicit": residual_ready,
        "tetrad_residual_in_allowed_basis": residual_ready and basis_ready,
        "tetrad_residual_ready_for_one_form_decomposition": residual_ready and basis_ready,
    }
    return {
        "status": "janus-z2-sigma-counterterm-tetrad-residual-channel-gate",
        "active_core": "Z2_tunnel_Sigma",
        "primary_sources_checked": [
            "first-order tetrad/Palatini variation",
            "Holst action tetrad-spin-connection variation",
            "Riemann-Cartan boundary term literature",
            "active coframe/connection pullback gate",
        ],
        "bibliography_result": (
            "Palatini-Holst literature supplies the independent coframe/tetrad "
            "variation channel. It does not compute the active Janus/Sigma residual "
            "coefficient R_e after tunnel pullback and Z2 orientation transport."
        ),
        "declared": declared,
        "closure": closure,
        "upstream_frontiers": {
            "tetrad_variation_transport": {
                "gate": transport_readiness["status"],
                "ready": transport_ready,
                "readiness": transport_readiness["readiness"],
                "current_frontier": transport_readiness["current_frontier"],
            },
            "local_density_basis": {
                "gate": local_basis["status"],
                "ready": basis_ready,
                "closure": local_basis["closure"],
                "allowed_basis": local_basis["allowed_basis"],
            },
            "metric_residual_coefficient_writer": {
                "gate": metric_coefficient_writer["status"],
                "ready": metric_coefficient_writer["gate_passed"],
                "output_manifest": metric_coefficient_writer["output_manifest"],
                "nearest_frontier": metric_coefficient_writer["nearest_frontier"],
            },
        },
        "channel_template": "alpha_e = integral_Sigma R_e^a_I delta e_a^I",
        "transport_targets": [
            "delta h_ab from delta e",
            "delta K_ab from delta e and active embedding",
            "delta torsion pullback from delta e and delta omega",
            "Z2 orientation sign policy",
        ],
        "partial_subchannels": {
            "metric": {
                "ready": metric_subchannel_ready,
                "status": "partial_only_not_one_form_ready",
                "formula": "delta h_ab = eta_IJ(e_a^I delta e_b^J + e_b^J delta e_a^I)",
                "residual_coefficient": "R_e_metric^{aI} = 2 R_h^{ab} eta^{IJ} e_bJ when R_h^{ab} is symmetric",
                "value_ready": metric_coefficient_writer[
                    "tetrad_metric_residual_coefficient_value_ready"
                ],
                "requires": [
                    "active metric residual tensor R_h^{ab}",
                    "active coframe trace e_bJ on Sigma",
                    "allowed local density basis transport",
                ],
            },
            "extrinsic_curvature": {
                "ready": transport_readiness["readiness"][
                    "extrinsic_curvature_variation_transport_ready"
                ],
                "status": "blocked_on_active_embedding_frame_connection_variation",
            },
            "torsion_pullback": {
                "ready": transport_readiness["readiness"][
                    "torsion_pullback_variation_transport_ready"
                ],
                "status": "blocked_on_sigma_pullback_allowed_basis",
            },
        },
        "forbidden": [
            "fit tetrad residual coefficient",
            "drop tetrad channel",
            "metric-only shortcut that bypasses coframe variation",
            "legacy Z4 tetrad residual import",
        ],
        "counterterm_tetrad_residual_channel_ledger_declared": all(declared.values()),
        "counterterm_tetrad_residual_channel_ready": all(declared.values()) and all(closure.values()),
        "current_frontier": [
            f"{key} = false"
            for key, ready in closure.items()
            if not ready
        ],
        "next_required": [
            "compute_R_e_from_active_sigma_boundary_variation",
            "transport_delta_e_to_delta_h_delta_K_delta_torsion",
            "express_R_e_in_allowed_local_density_basis",
            "feed_R_e_to_residual_one_form_decomposition_gate",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Counterterm Tetrad Residual Channel Gate",
        "",
        f"Active core: `{payload['active_core']}`",
        f"Ledger declared: `{payload['counterterm_tetrad_residual_channel_ledger_declared']}`",
        f"Channel ready: `{payload['counterterm_tetrad_residual_channel_ready']}`",
        "",
        f"Template: `{payload['channel_template']}`",
        "",
        "## Next Required",
    ]
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
