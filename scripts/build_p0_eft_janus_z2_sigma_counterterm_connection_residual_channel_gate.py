from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_counterterm_connection_residual_channel_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_counterterm_connection_residual_channel_gate.json")


def build_payload() -> dict:
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
        "connection_residual_coefficient_explicit": False,
        "connection_residual_in_allowed_basis": False,
        "connection_residual_ready_for_one_form_decomposition": False,
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
        "counterterm_connection_residual_channel_ready": all(declared.values()) and all(closure.values()),
        "next_required": [
            "compute_R_omega_from_active_sigma_boundary_variation",
            "transport_delta_omega_to_delta_torsion_pullback",
            "pass_counterterm_connection_variation_transport_gate",
            "express_R_omega_in_allowed_local_density_basis",
            "feed_R_omega_to_residual_one_form_decomposition_gate",
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
