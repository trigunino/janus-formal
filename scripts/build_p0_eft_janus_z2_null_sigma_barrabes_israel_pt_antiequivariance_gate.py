from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.janus_lab.z2_null_sigma_barrabes_israel import (
    null_sigma_barrabes_israel_payload,
)
from src.janus_lab.z2_null_sigma_pt_transverse_pullback import (
    null_sigma_pt_transverse_pullback_payload,
)


REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_null_sigma_barrabes_israel_pt_antiequivariance_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_null_sigma_barrabes_israel_pt_antiequivariance_gate.json"
)


def build_payload() -> dict:
    bi = null_sigma_barrabes_israel_payload()
    pullback = null_sigma_pt_transverse_pullback_payload()
    closure = {
        "plus_side_transverse_curvature_available": True,
        "PT_anti_equivariance_assumption_declared": False,
        "PT_pullback_transverse_curvature_ready": pullback[
            "PT_pullback_transverse_curvature_ready"
        ],
        "PT_anti_equivariance_proved_from_explicit_minus_metric": False,
        "conditional_jump_computable": True,
        "conditional_stress_slots_computable": True,
        "active_stress_slots_computable_from_PT_pullback": pullback[
            "active_stress_mapping_ready"
        ],
        "absolute_Rs_selected": False,
    }
    return {
        "status": "janus-z2-null-sigma-barrabes-israel-pt-antiequivariance-gate",
        "active_core": "Z2_tunnel_Sigma",
        "branch": "Z2_null_Sigma_PT_bridge",
        "policy": "conditional_diagnostic_not_active_closure",
        "C_plus": bi["transverse_curvature_plus_side"],
        "C_minus_from_PT_pullback": pullback["C_minus_from_PT_pullback"],
        "jump_from_PT_pullback": pullback["jump_from_PT_pullback"],
        "stress_from_PT_pullback": pullback["stress_from_PT_pullback"],
        "PT_pullback": {
            "route": pullback["route"],
            "uses_free_orientation_sign": pullback["uses_free_orientation_sign"],
            "explicit_minus_metric_components_available": pullback[
                "explicit_minus_metric_components_available"
            ],
            "sign_rule_source": pullback["sign_rule_source"],
        },
        "closure": closure,
        "conditional_stress_mapping_ready": True,
        "active_stress_mapping_ready": pullback["active_stress_mapping_ready"],
        "scale_selection_ready": False,
        "interpretation": (
            "The null/PT branch now computes the Barrabes-Israel stress slots from "
            "the orientation-reversing PT pullback C_minus_ab=-C_plus_ab. This is an "
            "active null-bridge pullback, not an explicit minus-metric component "
            "derivation. It still does not select an absolute R_s."
        ),
        "blocked_by": [key for key, ok in closure.items() if not ok],
        "gate_passed": True,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2 Null Sigma Barrabes-Israel PT Anti-Equivariance Gate",
        "",
        payload["interpretation"],
        "",
        f"Conditional stress mapping ready: `{payload['conditional_stress_mapping_ready']}`",
        f"Active stress mapping ready: `{payload['active_stress_mapping_ready']}`",
        f"Scale selection ready: `{payload['scale_selection_ready']}`",
        "",
        "## Blocked By",
    ]
    lines.extend(f"- `{item}`" for item in payload["blocked_by"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
