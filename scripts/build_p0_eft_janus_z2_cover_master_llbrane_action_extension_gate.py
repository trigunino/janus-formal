from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z2_null_sigma_llbrane_worldvolume_tension_selection_gate import (
    build_payload as build_worldvolume_selection,
)


REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_cover_master_llbrane_action_extension_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_cover_master_llbrane_action_extension_gate.json"
)


def build_payload() -> dict:
    worldvolume = build_worldvolume_selection()
    closure = {
        "active_core_JanusZ2CoverMasterAction": True,
        "single_master_action_retained": True,
        "LL_brane_worldvolume_added_on_Sigma": True,
        "LL_brane_marked_as_explicit_extension": True,
        "chi_LL_composite_tension_declared": worldvolume["closure"][
            "chi_composite_declared"
        ],
        "chi_LL_variation_included": True,
        "null_junction_variation_included": True,
        "horizon_straddling_condition_derived": worldvolume["closure"][
            "horizon_straddling_derived"
        ],
        "mass_radius_relation_derived": worldvolume["closure"][
            "einstein_matching_relates_m_to_chi"
        ],
        "chi_magnitude_selected_by_global_variation": False,
        "chi_magnitude_selected_by_boundary_state": False,
    }
    return {
        "status": "janus-z2-cover-master-llbrane-action-extension-gate",
        "active_core": "JanusZ2CoverMasterAction",
        "branch": "Z2_null_Sigma_PT_bridge",
        "extension_status": "explicit_LL_brane_source",
        "master_action_form": (
            "S_total = S_Z2_cover_master[g_hat,matter] "
            "+ S_LLbrane[X,gamma,A,chi; Sigma]"
        ),
        "variation_channels": {
            "delta_g_hat": "bulk plus Sigma distributional source",
            "delta_X_LL": "null embedding / horizon straddling equations",
            "delta_gamma_ab": "lightlike induced metric constraint",
            "delta_A_worldvolume": "dual field strength / tension conservation channel",
            "delta_measure_fields": "composite tension chi_LL channel",
        },
        "worldvolume_tension_selection": worldvolume,
        "closure": closure,
        "master_LLbrane_extension_ready": all(closure.values()),
        "blocked_by": [key for key, ok in closure.items() if not ok],
        "interpretation": (
            "Adding S_LLbrane to the Janus cover master action is coherent as an "
            "explicit extension and supplies the Sigma null source. The combined "
            "variation still does not select the absolute chi_LL magnitude unless "
            "a Janus boundary-state, quantization or superselection condition is "
            "added."
        ),
        "next_required": [
            "derive_boundary_state_or_quantization_condition_for_chi_LL",
            "or_accept_chi_LL_as_explicit_extension_state_input",
        ],
        "forbidden_shortcuts": [
            "do_not_treat_LLbrane_extension_as_strict_no_extension",
            "do_not_set_chi_LL_by_observational_fit",
            "do_not_claim_global_variation_fixes_chi_without_state_condition",
        ],
        "gate_passed": False,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2 Cover Master LL-Brane Action Extension Gate",
        "",
        payload["interpretation"],
        "",
        f"Extension ready: `{payload['master_LLbrane_extension_ready']}`",
        "",
        "## Blocked By",
    ]
    lines.extend(f"- `{item}`" for item in payload["blocked_by"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
