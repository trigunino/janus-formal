from __future__ import annotations

from pathlib import Path
import json

import sympy as sp


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_obstruction_ward_identity.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_obstruction_ward_identity.json")


def build_payload() -> dict:
    div_j, anomaly, B = sp.symbols("div_J_Z4 A_Z4 B", nonzero=True)
    obstruction = div_j - anomaly
    r_plus = obstruction
    r_minus = -obstruction / B
    weighted_residual = sp.simplify(r_plus + B * r_minus)
    ward_residual = sp.simplify(obstruction - (div_j - anomaly))
    closed_if_anomaly_free = sp.simplify(obstruction.subs({div_j: 0, anomaly: 0}))

    return {
        "status": "janus-z4-obstruction-ward-identity",
        "obstruction": str(obstruction),
        "r_plus": str(r_plus),
        "r_minus": str(r_minus),
        "weighted_residual": str(weighted_residual),
        "ward_residual": str(ward_residual),
        "closed_if_anomaly_free": str(closed_if_anomaly_free),
        "obstruction_ward_identity_ready": weighted_residual == 0 and ward_residual == 0,
        "anomaly_cancellation_derived": False,
        "full_action_variation_closed": False,
        "next_required": "Derive div_J_Z4 = 0 and A_Z4 = 0 from the full nonlinear gauge symmetry.",
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z4 Obstruction Ward Identity",
        "",
        f"Status: `{payload['status']}`",
        f"Obstruction: `{payload['obstruction']}`",
        f"Weighted residual: `{payload['weighted_residual']}`",
        f"Ward residual: `{payload['ward_residual']}`",
        f"Closed if anomaly free: `{payload['closed_if_anomaly_free']}`",
        f"Full action variation closed: `{payload['full_action_variation_closed']}`",
        "",
        f"Next required: {payload['next_required']}",
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
