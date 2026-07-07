from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path(
    "outputs/reports/"
    "p0_eft_janus_z2_null_sigma_llbrane_worldvolume_tension_selection_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/"
    "p0_eft_janus_z2_null_sigma_llbrane_worldvolume_tension_selection_gate.json"
)


def build_payload() -> dict:
    closure = {
        "worldvolume_action_declared": True,
        "chi_composite_declared": True,
        "auxiliary_measure_equation_declared": True,
        "a0_consistency_fixed": True,
        "horizon_straddling_derived": True,
        "einstein_matching_relates_m_to_chi": True,
        "chi_magnitude_selected_by_local_worldvolume_eom": False,
        "chi_magnitude_selected_by_Janus_PT_boundary_state": False,
        "chi_abs_inverse_m_available": False,
    }
    return {
        "status": "janus-z2-null-sigma-llbrane-worldvolume-tension-selection-gate",
        "active_core": "Z2_tunnel_Sigma",
        "branch": "Z2_null_Sigma_PT_bridge",
        "extension_status": "explicit_LL_brane_source_frontier",
        "source_basis": {
            "action": "S_LL = - integral Phi [1/2 gamma^ab g_ab - L(F^2)]",
            "dynamical_tension": "chi = Phi/sqrt(-gamma)",
            "measure_equation": "1/2 gamma^ab g_ab - L(F^2) = M_integration",
            "a0": "a0 = F^2 L'(F^2)|on-shell = 1/8 after matching",
            "mass_matching": "m = 1/(16*pi*abs(chi_LL))",
        },
        "closure": closure,
        "worldvolume_selection_ready": all(closure.values()),
        "blocked_by": [key for key, ok in closure.items() if not ok],
        "interpretation": (
            "The LL-brane worldvolume equations make chi_LL a dynamical composite "
            "tension and fix a0 by matching, but they do not select the absolute "
            "magnitude of chi_LL. That magnitude remains a Janus boundary-state, "
            "superselection or extra worldvolume-sector datum."
        ),
        "next_required": [
            "derive_Janus_PT_boundary_state_condition_for_chi_LL",
            "or_derive_quantization_superselection_law_for_chi_LL",
            "or_accept_chi_LL_as_explicit_extension_state_input",
        ],
        "forbidden_shortcuts": [
            "do_not_set_chi_LL_by_observation",
            "do_not_claim_local_LL_worldvolume_EOM_selects_chi_magnitude",
            "do_not_promote_extension_as_no_extension_closure",
        ],
        "gate_passed": False,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2 Null Sigma LL-Brane Worldvolume Tension Selection Gate",
        "",
        payload["interpretation"],
        "",
        f"Worldvolume selection ready: `{payload['worldvolume_selection_ready']}`",
        "",
        "## Blocked By",
    ]
    lines.extend(f"- `{item}`" for item in payload["blocked_by"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
