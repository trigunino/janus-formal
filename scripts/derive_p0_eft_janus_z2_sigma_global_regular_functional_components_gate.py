from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.derive_p0_eft_janus_z2_sigma_global_regular_tunnel_radius_selection_gate import (
    build_payload as build_radius_selection_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_resolved_tunnel_smooth_atlas_gate import (
    build_payload as build_smooth_atlas_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_tunnel_junction_condition_gate import (
    build_payload as build_junction_payload,
)


REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_global_regular_functional_components_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_global_regular_functional_components_gate.json"
)


def build_payload() -> dict:
    selection = build_radius_selection_payload()
    atlas = build_smooth_atlas_payload()
    junction = build_junction_payload()
    components = {
        "normal_frame_holonomy_defect": {
            "formula": "||P exp(int_collar omega_perp) - Id||^2",
            "requires": ["normal_connection_on_active_collar", "closed_collar_cycle"],
            "ready": False,
        },
        "collar_endpoint_mismatch": {
            "formula": "||tau_Z2^* h_minus|endpoint - h_plus|endpoint||^2",
            "requires": ["active_plus_minus_collar_metrics", "projective_deck_pullback"],
            "ready": False,
        },
        "junction_bianchi_defect": {
            "formula": "||D_a S_Sigma^{ab} + [T_{n}^{b}]_Z2||^2",
            "requires": ["surface_stress_tensor", "bulk_normal_flux_jump", "active_connection"],
            "ready": False,
        },
    }
    upstream = {
        "selection_target_declared": selection["derived_now"][
            "global_regular_selection_functional_declared"
        ],
        "smooth_atlas_ready": atlas["resolved_tunnel_smooth_atlas_ready"],
        "junction_condition_declared": junction["z2_tunnel_junction_condition_derived"],
    }
    all_components_ready = all(item["ready"] for item in components.values())
    return {
        "status": "janus-z2-sigma-global-regular-functional-components-gate",
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_symbolic_audit",
        "lambda_symbol": selection["lambda_symbol"],
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_reuse_used": False,
        "observational_fit_used": False,
        "torus_replacement_used": False,
        "full_no_fit_prediction_ready": False,
        "upstream": upstream,
        "F_reg_components": components,
        "F_reg_formula": (
            "F_reg = normal_frame_holonomy_defect + "
            "collar_endpoint_mismatch + junction_bianchi_defect"
        ),
        "F_reg_value_ready": all_components_ready,
        "radius_selection_ready": all_components_ready,
        "gate_passed": True,
        "primary_blocker": "active_collar_metric_connection_and_flux_data"
        if not all_components_ready
        else "none",
        "next_required": [
            "derive active plus/minus collar metrics h_pm(lambda_Sigma,u)",
            "derive active normal connection omega_perp(lambda_Sigma,u)",
            "derive Z2 deck pullback on endpoint collar data",
            "derive S_Sigma_ab and bulk normal flux jump for Bianchi residual",
        ]
        if not all_components_ready
        else [],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Global Regular Functional Components Gate",
        "",
        f"Lambda: `{payload['lambda_symbol']}`",
        f"F_reg ready: `{payload['F_reg_value_ready']}`",
        f"Primary blocker: `{payload['primary_blocker']}`",
        "",
        "## Components",
    ]
    for name, item in payload["F_reg_components"].items():
        lines.append(f"- `{name}` ready=`{item['ready']}` formula=`{item['formula']}`")
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
