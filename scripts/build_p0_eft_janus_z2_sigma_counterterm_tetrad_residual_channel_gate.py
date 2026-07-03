from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_counterterm_tetrad_residual_channel_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_counterterm_tetrad_residual_channel_gate.json")


def build_payload() -> dict:
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
    closure = {
        "tetrad_residual_coefficient_explicit": False,
        "tetrad_residual_in_allowed_basis": False,
        "tetrad_residual_ready_for_one_form_decomposition": False,
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
        "channel_template": "alpha_e = integral_Sigma R_e^a_I delta e_a^I",
        "transport_targets": [
            "delta h_ab from delta e",
            "delta K_ab from delta e and active embedding",
            "delta torsion pullback from delta e and delta omega",
            "Z2 orientation sign policy",
        ],
        "forbidden": [
            "fit tetrad residual coefficient",
            "drop tetrad channel",
            "metric-only shortcut that bypasses coframe variation",
            "legacy Z4 tetrad residual import",
        ],
        "counterterm_tetrad_residual_channel_ledger_declared": all(declared.values()),
        "counterterm_tetrad_residual_channel_ready": all(declared.values()) and all(closure.values()),
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
