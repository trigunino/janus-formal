from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_counterterm_residual_channel_frontier_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_counterterm_residual_channel_frontier_gate.json")


def build_payload() -> dict:
    declared = {
        "tetrad_residual_channel_imported": True,
        "connection_residual_channel_imported": True,
        "spinor_residual_channel_imported": True,
        "embedding_residual_channel_imported": True,
        "matter_flux_residual_channel_imported": True,
        "variational_bicomplex_bibliography_checked": True,
        "no_fitted_residual_coefficient": True,
    }
    channels = {
        "tetrad_residual_ready": False,
        "connection_residual_ready": False,
        "spinor_residual_ready": False,
        "embedding_residual_ready": False,
        "matter_flux_residual_ready": False,
        "all_residual_channels_explicit": False,
        "residual_one_form_ready_for_decomposition": False,
    }
    return {
        "status": "janus-z2-sigma-counterterm-residual-channel-frontier-gate",
        "active_core": "Z2_tunnel_Sigma",
        "primary_sources_checked": [
            "covariant phase space / variational bicomplex boundary one-form split",
            "Palatini-Holst coframe and spin-connection variation",
            "Dirac boundary variation and projected spinor channels",
            "thin-shell embedding and matter-flux variation channels",
        ],
        "source_links": [
            "https://arxiv.org/abs/1806.01529",
            "https://arxiv.org/abs/gr-qc/9209012",
            "https://link.springer.com/article/10.1007/BF02710419",
        ],
        "bibliography_result": (
            "The field-space one-form split is standard. The active Janus/Sigma task is "
            "to compute each residual coefficient in the allowed local basis; no channel "
            "may be dropped or fitted."
        ),
        "declared": declared,
        "channels": channels,
        "channel_coefficients": [
            "R_e tetrad/coframe coefficient",
            "R_omega spin-connection coefficient",
            "R_psi and R_psibar projected spinor coefficients",
            "R_X embedding coefficient",
            "R_matter matter-flux coefficient",
        ],
        "residual_channel_frontier_ledger_declared": all(declared.values()),
        "residual_channel_frontier_ready": all(declared.values()) and all(channels.values()),
        "current_frontier": [
            "tetrad_residual_ready = false",
            "connection_residual_ready = false",
            "spinor_residual_ready = false",
            "embedding_residual_ready = false",
            "matter_flux_residual_ready = false",
        ],
        "next_required": [
            "close_tetrad_residual_channel_gate",
            "close_connection_residual_channel_gate",
            "close_spinor_residual_channel_gate",
            "close_embedding_residual_channel_gate",
            "close_matter_flux_residual_channel_gate",
            "feed_all_coefficients_to_residual_one_form_decomposition_gate",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Counterterm Residual Channel Frontier Gate",
        "",
        f"Active core: `{payload['active_core']}`",
        f"Ledger declared: `{payload['residual_channel_frontier_ledger_declared']}`",
        f"Channel frontier ready: `{payload['residual_channel_frontier_ready']}`",
        "",
        "## Channel Coefficients",
    ]
    lines.extend(f"- `{item}`" for item in payload["channel_coefficients"])
    lines.extend(["", "## Current Frontier"])
    lines.extend(f"- `{item}`" for item in payload["current_frontier"])
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
