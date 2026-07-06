from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_deck_normal_frame_action_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_deck_normal_frame_action_gate.json")


def build_payload() -> dict:
    return {
        "status": "janus-z2-sigma-deck-normal-frame-action-gate",
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_symbolic_audit",
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_reuse_used": False,
        "observational_fit_used": False,
        "torus_replacement_used": False,
        "full_no_fit_prediction_ready": False,
        "deck_action": {
            "tau_Z2_swaps_sides": True,
            "tau_Z2_reverses_collar_normal": True,
            "normal_line_deck_matrix": [[-1.0]],
            "normal_orientation_condition": "tau_Z2^* n_+ = - n_-",
        },
        "derived_now": {
            "deck_frame_map_lambda_ready": True,
            "collar_connection_omega_perp_ready": False,
            "deck_corrected_holonomy_ready": False,
            "R_Sigma_over_ell_collar_fixed": False,
        },
        "gate_passed": True,
        "primary_blocker": "collar_connection_from_active_metric_not_derived",
        "next_required": [
            "derive omega_perp(lambda,u) from active collar metric",
            "compute D_Z2 Pexp(int omega_perp du)",
            "solve the deck-corrected holonomy condition",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(
        "\n".join(
            [
                "# Janus Z2/Sigma Deck Normal Frame Action Gate",
                "",
                f"Deck frame ready: `{payload['derived_now']['deck_frame_map_lambda_ready']}`",
                f"Primary blocker: `{payload['primary_blocker']}`",
                f"Normal line deck matrix: `{payload['deck_action']['normal_line_deck_matrix']}`",
            ]
        ),
        encoding="utf-8",
    )
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
