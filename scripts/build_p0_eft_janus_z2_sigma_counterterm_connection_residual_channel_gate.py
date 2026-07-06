from __future__ import annotations

import json
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from scripts.build_p0_eft_janus_z2_sigma_counterterm_connection_variation_transport_gate import (
    build_payload as build_connection_variation_transport_payload,
)

COEFF_PATH = Path("outputs/active_z2_sigma/counterterm_residual_coefficients_partial.json")


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_counterterm_connection_residual_channel_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_counterterm_connection_residual_channel_gate.json")


def build_payload() -> dict:
    transport = build_connection_variation_transport_payload()
    coeff = json.loads(COEFF_PATH.read_text(encoding="utf-8")) if COEFF_PATH.exists() else {}
    fixed_commutation_ready = transport["partial_subchannels"]["fixed_embedding_commutation"][
        "ready"
    ]
    transport_ready = transport["counterterm_connection_variation_transport_ready"]
    torsion_pullback_coeff_zero = bool(
        coeff.get("R_T_A_ready")
        and all(
            float(value) == 0.0
            for block in coeff.get("R_T_A_values", [])
            for row in block
            for value in row
        )
    )
    connection_residual_zero = fixed_commutation_ready and torsion_pullback_coeff_zero
    declared = {
        "coframe_connection_pullback_gate_declared": True,
        "torsion_pullback_on_sigma_gate_declared": True,
        "holst_nieh_yan_radial_block_gate_declared": True,
        "connection_variation_transport_gate_declared": True,
        "palatini_holst_connection_variation_bibliography_checked": True,
        "spin_connection_variation_basis_declared": True,
        "connection_residual_channel_problem_declared": True,
        "torsion_variation_transport_declared": True,
        "nieh_yan_boundary_variation_transport_declared": True,
        "z2_orientation_variation_policy_declared": True,
        "no_fitted_connection_residual_coefficient": True,
    }
    closure = {
        "fixed_embedding_commutation_subchannel_ready": fixed_commutation_ready,
        "connection_variation_transport_ready": transport_ready,
        "torsion_pullback_coefficient_zero": torsion_pullback_coeff_zero,
        "connection_residual_coefficient_explicit": connection_residual_zero,
        "connection_residual_in_allowed_basis": connection_residual_zero,
        "connection_residual_ready_for_one_form_decomposition": connection_residual_zero,
    }
    return {
        "status": "janus-z2-sigma-counterterm-connection-residual-channel-gate",
        "active_core": "Z2_tunnel_Sigma",
        "primary_sources_checked": [
            "first-order Palatini spin-connection variation",
            "Holst action connection variation",
            "Nieh-Yan boundary variation",
            "active torsion pullback on Sigma gate",
            "active connection variation transport gate",
        ],
        "bibliography_result": (
            "Palatini-Holst/Nieh-Yan literature supplies the independent connection "
            "variation channel. It does not compute the active Janus/Sigma residual "
            "coefficient R_omega after torsion pullback and Z2 orientation transport."
        ),
        "declared": declared,
        "closure": closure,
        "residual_coefficient": {
            "R_omega": "0" if connection_residual_zero else "unresolved",
            "scope": "connection_only_fixed_embedding_torsionless_sigma_branch",
            "provenance": (
                "delta_omega holds X_Sigma fixed, pullback commutes with delta_omega, "
                "and the active torsion-pullback residual coefficient R_T^A is zero"
            ),
            "full_connection_transport_claimed": transport_ready,
        },
        "upstream_frontiers": {
            "connection_variation_transport": {
                "gate": transport["status"],
                "ready": transport_ready,
                "closure": transport["closure"],
                "partial_subchannels": transport["partial_subchannels"],
            },
        },
        "partial_subchannels": {
            "fixed_embedding_commutation_to_connection_channel": {
                "ready": fixed_commutation_ready,
                "status": "partial_only_not_R_omega_explicit",
                "formula": "delta_omega X_Sigma^* omega = X_Sigma^*(delta_omega omega)",
            },
        },
        "channel_template": "alpha_omega = integral_Sigma R_omega^{ab} delta omega_ab",
        "transport_targets": [
            "delta torsion pullback from delta omega",
            "delta Nieh-Yan boundary density from delta omega",
            "connection pullback orientation under Z2",
            "compatibility with tetrad channel variation",
        ],
        "forbidden": [
            "fit connection residual coefficient",
            "drop connection channel",
            "torsion-free shortcut before Cartan equation",
            "legacy Z4 connection residual import",
        ],
        "counterterm_connection_residual_channel_ledger_declared": all(declared.values()),
        "counterterm_connection_residual_channel_ready": all(declared.values())
        and closure["fixed_embedding_commutation_subchannel_ready"]
        and closure["connection_residual_coefficient_explicit"]
        and closure["connection_residual_in_allowed_basis"]
        and closure["connection_residual_ready_for_one_form_decomposition"],
        "next_required": [
            *([] if connection_residual_zero else [
                "compute_R_omega_from_active_sigma_boundary_variation",
                "transport_delta_omega_to_delta_torsion_pullback",
                "pass_counterterm_connection_variation_transport_gate",
                "express_R_omega_in_allowed_local_density_basis",
                "feed_R_omega_to_residual_one_form_decomposition_gate",
            ]),
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Counterterm Connection Residual Channel Gate",
        "",
        f"Active core: `{payload['active_core']}`",
        f"Ledger declared: `{payload['counterterm_connection_residual_channel_ledger_declared']}`",
        f"Channel ready: `{payload['counterterm_connection_residual_channel_ready']}`",
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
