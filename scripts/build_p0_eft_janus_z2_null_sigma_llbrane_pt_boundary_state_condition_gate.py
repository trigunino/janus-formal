from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path(
    "outputs/reports/"
    "p0_eft_janus_z2_null_sigma_llbrane_pt_boundary_state_condition_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/"
    "p0_eft_janus_z2_null_sigma_llbrane_pt_boundary_state_condition_gate.json"
)


def build_payload() -> dict:
    closure = {
        "PT_sheet_exchange_declared": True,
        "PT_energy_mass_sign_reversal_declared": True,
        "global_boundary_state_invariant_under_PT": True,
        "net_PT_pair_charge_zero": True,
        "chi_LL_sign_fixed_negative": True,
        "chi_LL_constant_on_Sigma": True,
        "chi_LL_magnitude_fixed_by_PT_invariance": False,
        "absolute_Rs_fixed_by_PT_boundary_state": False,
    }
    return {
        "status": "janus-z2-null-sigma-llbrane-pt-boundary-state-condition-gate",
        "active_core": "Z2_tunnel_Sigma",
        "branch": "Z2_null_Sigma_PT_bridge",
        "extension_status": "explicit_LL_brane_source_frontier",
        "condition": {
            "state": "Psi_total is invariant under PT sheet exchange",
            "mass_pairing": "M_minus = -M_plus",
            "tension_sign": "chi_LL < 0 for the ER/LL-brane matching branch",
            "boundary_charge": "Q_plus + Q_minus = 0",
        },
        "closure": closure,
        "PT_boundary_state_selects_chi": all(closure.values()),
        "blocked_by": [key for key, ok in closure.items() if not ok],
        "interpretation": (
            "The PT boundary-state condition fixes the sign sector, sheet pairing, "
            "and constancy class of chi_LL. It does not fix the absolute magnitude "
            "of chi_LL, because rescaling the paired mass/tension preserves the PT "
            "invariance and zero total charge."
        ),
        "next_required": [
            "add_independent_state_label_or_quantization_condition_for_chi_LL",
            "or_accept_chi_LL_as_extension_state_input",
        ],
        "gate_passed": False,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2 Null Sigma LL-Brane PT Boundary State Condition Gate",
        "",
        payload["interpretation"],
        "",
        f"PT boundary state selects chi: `{payload['PT_boundary_state_selects_chi']}`",
        "",
        "## Blocked By",
    ]
    lines.extend(f"- `{item}`" for item in payload["blocked_by"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
