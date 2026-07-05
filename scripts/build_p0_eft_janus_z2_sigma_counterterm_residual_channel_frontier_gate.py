from __future__ import annotations

import json
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from scripts.build_p0_eft_janus_z2_sigma_counterterm_connection_residual_channel_gate import (
    build_payload as build_connection_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_counterterm_embedding_residual_channel_gate import (
    build_payload as build_embedding_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_counterterm_matter_flux_residual_channel_gate import (
    build_payload as build_matter_flux_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_counterterm_spinor_residual_channel_gate import (
    build_payload as build_spinor_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_counterterm_tetrad_residual_channel_gate import (
    build_payload as build_tetrad_payload,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_counterterm_residual_channel_frontier_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_counterterm_residual_channel_frontier_gate.json")


def build_payload() -> dict:
    tetrad = build_tetrad_payload()
    connection = build_connection_payload()
    spinor = build_spinor_payload()
    embedding = build_embedding_payload()
    matter_flux = build_matter_flux_payload()
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
        "tetrad_residual_ready": tetrad["counterterm_tetrad_residual_channel_ready"],
        "connection_residual_ready": connection["counterterm_connection_residual_channel_ready"],
        "spinor_residual_ready": spinor["counterterm_spinor_residual_channel_ready"],
        "embedding_residual_ready": embedding["counterterm_embedding_residual_channel_ready"],
        "matter_flux_residual_ready": matter_flux["counterterm_matter_flux_residual_channel_ready"],
    }
    channels["all_residual_channels_explicit"] = all(channels.values())
    channels["residual_one_form_ready_for_decomposition"] = channels[
        "all_residual_channels_explicit"
    ]
    channel_frontiers = {
        "tetrad": {
            "gate": tetrad["status"],
            "ready": tetrad["counterterm_tetrad_residual_channel_ready"],
            "closure": tetrad["closure"],
        },
        "connection": {
            "gate": connection["status"],
            "ready": connection["counterterm_connection_residual_channel_ready"],
            "closure": connection["closure"],
        },
        "spinor": {
            "gate": spinor["status"],
            "ready": spinor["counterterm_spinor_residual_channel_ready"],
            "closure": spinor["closure"],
        },
        "embedding": {
            "gate": embedding["status"],
            "ready": embedding["counterterm_embedding_residual_channel_ready"],
            "closure": embedding["closure"],
        },
        "matter_flux": {
            "gate": matter_flux["status"],
            "ready": matter_flux["counterterm_matter_flux_residual_channel_ready"],
            "closure": matter_flux["closure"],
        },
    }
    partial_scores = {
        name: sum(1 for value in data["closure"].values() if value is True)
        for name, data in channel_frontiers.items()
    }
    nearest_channel = max(partial_scores, key=partial_scores.get)
    ready = all(declared.values()) and all(channels.values())
    if ready:
        primary_blocker = "none"
    elif (
        nearest_channel == "tetrad"
        and tetrad["closure"]["tetrad_variation_transport_ready"]
        and tetrad["closure"]["active_sigma_boundary_variation_residual_formula_ready"]
        and not tetrad["closure"]["tetrad_residual_coefficient_explicit"]
    ):
        primary_blocker = "tetrad_residual_coefficients"
    else:
        primary_blocker = f"{nearest_channel}_residual_channel"
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
        "channel_frontiers": channel_frontiers,
        "partial_channel_scores": partial_scores,
        "nearest_residual_channel_frontier": {
            "channel": nearest_channel,
            "reason": (
                "highest number of already explicit closure subchannels; this is an "
                "attack order hint, not a proof of readiness"
            ),
            "transport_closed_coefficients_open": primary_blocker
            == "tetrad_residual_coefficients",
            "score": partial_scores[nearest_channel],
            "remaining_false_closure_fields": [
                key
                for key, value in channel_frontiers[nearest_channel]["closure"].items()
                if value is False
            ],
        },
        "channel_coefficients": [
            "R_e tetrad/coframe coefficient",
            "R_omega spin-connection coefficient",
            "R_psi and R_psibar projected spinor coefficients",
            "R_X embedding coefficient",
            "R_matter matter-flux coefficient",
        ],
        "residual_channel_frontier_ledger_declared": all(declared.values()),
        "nearest_residual_channel_frontier_declared": True,
        "nearest_residual_channel_frontier_is_diagnostic_only": True,
        "residual_channel_frontier_ready": ready,
        "gate_passed": ready,
        "primary_blocker": primary_blocker,
        "current_frontier": [
            f"{key} = false"
            for key, ready in channels.items()
            if not ready and key.endswith("_ready")
        ],
        "next_required": [
            "derive_tetrad_residual_coefficients_R_h_R_K_R_T_R_chi",
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
    lines.extend(
        [
            "",
            "## Nearest Residual Channel Frontier",
            f"`{payload['nearest_residual_channel_frontier']['channel']}`",
        ]
    )
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
