from __future__ import annotations

import json
import sys
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z2_llbrane_global_state_matching_gate import (
    build_payload as build_global_matching_payload,
)
from scripts.build_p0_eft_janus_z2_null_sigma_llbrane_flux_quantization_relation_audit_gate import (
    build_payload as build_flux_payload,
)
from scripts.build_p0_eft_janus_z2_null_sigma_llbrane_pt_boundary_state_condition_gate import (
    build_payload as build_pt_payload,
)
from scripts.build_p0_eft_janus_z2_null_sigma_llbrane_worldvolume_tension_selection_gate import (
    build_payload as build_worldvolume_payload,
)


REPORT_PATH = Path(
    "outputs/reports/"
    "p0_eft_janus_z2_null_sigma_llbrane_chi_selection_exhaustive_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/"
    "p0_eft_janus_z2_null_sigma_llbrane_chi_selection_exhaustive_gate.json"
)


def _blocked(payload: dict[str, Any]) -> list[str]:
    return list(payload.get("blocked_by", []))


def build_payload() -> dict[str, Any]:
    worldvolume = build_worldvolume_payload()
    pt_boundary = build_pt_payload()
    flux = build_flux_payload()
    global_matching = build_global_matching_payload()

    route_status = {
        "worldvolume_local_eom": {
            "closes_chi_LL": bool(worldvolume["worldvolume_selection_ready"]),
            "blocked_by": _blocked(worldvolume),
            "result": "chi_LL is composite and constant, magnitude not selected",
        },
        "PT_boundary_state": {
            "closes_chi_LL": bool(pt_boundary["PT_boundary_state_selects_chi"]),
            "blocked_by": _blocked(pt_boundary),
            "result": "PT fixes sign, pairing, and constancy, not magnitude",
        },
        "S2_flux_quantization": {
            "closes_chi_LL": bool(flux["flux_relation_closes_chi"]),
            "blocked_by": _blocked(flux),
            "result": "flux quantization is conditional on q_LL, area gauge, and F2_0",
        },
        "global_mass_chi_matching": {
            "closes_chi_LL": bool(global_matching["absolute_scale_selected"]),
            "blocked_by": list(global_matching["next_required"]),
            "result": "M_bridge and chi_LL are one scale, not two independent scales",
        },
    }
    closed_routes = [
        name for name, status in route_status.items() if status["closes_chi_LL"]
    ]
    remaining_nonfit_exits = [
        "derive q_LL, physical S2 area gauge, and F2_0 from a Janus LL gauge sector",
        "derive an absolute global bimetric/Noether mass state and match it to chi_LL",
        "declare chi_LL as an explicit extension-state input with clean non-observational provenance",
    ]
    all_current_routes_exhausted = len(closed_routes) == 0
    return {
        "status": "janus-z2-null-sigma-llbrane-chi-selection-exhaustive-gate",
        "active_core": "Z2_tunnel_Sigma",
        "branch": "Z2_null_Sigma_PT_bridge",
        "question": "Can current non-fit routes select chi_LL_abs_inverse_m?",
        "route_status": route_status,
        "closed_routes": closed_routes,
        "all_current_nonfit_routes_exhausted": all_current_routes_exhausted,
        "chi_LL_abs_inverse_m_ready": False,
        "M_bridge_ready_from_chi": bool(global_matching["reduces_two_parameters_to_one"]),
        "one_scale_policy": "chi_LL and M_bridge must not be treated as independent knobs",
        "remaining_nonfit_exits": remaining_nonfit_exits,
        "forbidden_shortcuts": [
            "do_not_fit_chi_LL_to_observations",
            "do_not_promote_PT_sign_pairing_to_magnitude_selection",
            "do_not_use_flux_quantization_without q_LL, area gauge, and F2_0",
            "do_not_keep_chi_LL_and_M_bridge_independent",
        ],
        "gate_passed": False,
    }


def write_reports() -> dict[str, Any]:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2 Null Sigma LL-Brane Chi Selection Exhaustive Gate",
        "",
        f"All current non-fit routes exhausted: `{payload['all_current_nonfit_routes_exhausted']}`",
        f"chi_LL_abs_inverse_m ready: `{payload['chi_LL_abs_inverse_m_ready']}`",
        "",
        "## Route Status",
    ]
    for name, status in payload["route_status"].items():
        lines.extend(
            [
                f"- `{name}`: closes chi = `{status['closes_chi_LL']}`; {status['result']}",
            ]
        )
    lines.extend(["", "## Remaining Non-Fit Exits"])
    lines.extend(f"- {item}" for item in payload["remaining_nonfit_exits"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
