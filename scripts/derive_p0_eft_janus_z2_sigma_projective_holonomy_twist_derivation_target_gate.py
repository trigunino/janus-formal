from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.derive_p0_eft_janus_z2_sigma_deck_normal_frame_action_gate import (
    build_payload as build_deck_action_payload,
)

REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_projective_holonomy_twist_derivation_target_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_projective_holonomy_twist_derivation_target_gate.json"
)


def build_payload() -> dict:
    deck = build_deck_action_payload()
    obligations = {
        "deck_action_on_normal_frame": {
            "target": "tau_Z2^* n_+ = -n_- plus induced action on normal frame bundle",
            "derived": deck["derived_now"]["deck_frame_map_lambda_ready"],
        },
        "collar_connection_from_active_metric": {
            "target": "omega_perp(lambda,u) = <N_A, D_u N_B> from active collar normal frame and metric",
            "derived": False,
            "calculator_available": True,
            "calculator": "build_p0_eft_janus_z2_sigma_normal_connection_from_frame_gate.py",
            "missing_manifest": "outputs/active_z2_sigma/normal_connection_frame_primitives.json",
        },
        "global_loop_closure": {
            "target": "P exp(int omega_perp du) composed with deck frame map = Id",
            "derived": False,
        },
        "non_flat_lambda_dependence": {
            "target": "normal holonomy defect is a non-flat function of R_Sigma/ell_collar",
            "derived": False,
        },
    }
    next_required = []
    if not obligations["deck_action_on_normal_frame"]["derived"]:
        next_required.append("derive deck action on the normal frame bundle")
    next_required.extend(
        [
            "derive omega_perp(lambda,u) from the active collar metric",
            "materialize normal_connection_frame_primitives.json for the active collar",
            "include deck-frame map in the global collar loop holonomy",
            "prove the resulting F_reg(lambda) is non-flat and has a unique root",
        ]
    )
    return {
        "status": "janus-z2-sigma-projective-holonomy-twist-derivation-target-gate",
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_symbolic_audit",
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_reuse_used": False,
        "observational_fit_used": False,
        "torus_replacement_used": False,
        "full_no_fit_prediction_ready": False,
        "diagnostic_probe_available": True,
        "diagnostic_probe_is_proof": False,
        "obligations": obligations,
        "projective_holonomy_twist_derived": all(item["derived"] for item in obligations.values()),
        "R_Sigma_over_ell_collar_selection_promotable": False,
        "gate_passed": True,
        "primary_blocker": "derive_deck_corrected_normal_holonomy_from_active_collar_metric",
        "next_required": next_required,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Projective Holonomy Twist Derivation Target Gate",
        "",
        f"Twist derived: `{payload['projective_holonomy_twist_derived']}`",
        f"Selection promotable: `{payload['R_Sigma_over_ell_collar_selection_promotable']}`",
        f"Primary blocker: `{payload['primary_blocker']}`",
        "",
        "## Obligations",
    ]
    for name, item in payload["obligations"].items():
        lines.append(f"- `{name}` derived=`{item['derived']}` target=`{item['target']}`")
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
