from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_aps_pin_projected_charge_selection_audit_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_aps_pin_projected_charge_selection_audit_gate.json"
)


def build_payload() -> dict:
    return {
        "status": "janus-z2-sigma-aps-pin-projected-charge-selection-audit-gate",
        "active_core": "Z2_tunnel_Sigma",
        "route": "APS/Pin/Z2 selection of projected Dirac charge",
        "aps_pin_can_fix": {
            "parity_anomaly_cancellation": True,
            "eta_regularization_channel": True,
            "trace_normalization_eta_H": True,
            "allowed_charge_parity_or_integrality_class": True,
        },
        "aps_pin_cannot_fix_without_state_input": {
            "absolute_fermion_occupation_number": True,
            "absolute_projected_baryon_Noether_charge": True,
            "baryon_to_photon_ratio": True,
            "baryon_number_density0_m3_Z2Sigma": True,
        },
        "reason": (
            "APS/Pin data can constrain spectral parity, anomaly cancellation and "
            "integer classes. It does not select which occupied Dirac state or net "
            "baryon charge the universe contains."
        ),
        "gate_passed": True,
        "projected_charge_solution_ready": False,
        "primary_blocker": "state_or_occupation_selection_not_fixed_by_APS_Pin",
        "next_required": [
            "derive a Janus state-selection theorem for occupied modes",
            "or accept projected baryon charge as initial data",
            "or restrict to observables independent of baryon normalization",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma APS/Pin Projected Charge Selection Audit Gate",
        "",
        f"Primary blocker: `{payload['primary_blocker']}`",
        f"Projected charge solution ready: `{payload['projected_charge_solution_ready']}`",
        "",
        payload["reason"],
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
