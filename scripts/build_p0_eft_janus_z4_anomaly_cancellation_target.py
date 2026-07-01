from __future__ import annotations

from pathlib import Path
import json

import sympy as sp


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_anomaly_cancellation_target.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_anomaly_cancellation_target.json")


def build_payload() -> dict:
    a_bulk, a_measure, div_j = sp.symbols("A_bulk A_measure div_J_Z4")
    a_boundary = -a_bulk
    total_anomaly = sp.simplify(a_bulk + a_boundary + a_measure)
    residual_after_measure = sp.simplify(total_anomaly.subs(a_measure, 0))
    obstruction_after_anomaly = sp.simplify(div_j - residual_after_measure)
    obstruction_if_current_conserved = sp.simplify(obstruction_after_anomaly.subs(div_j, 0))

    return {
        "status": "janus-z4-anomaly-cancellation-target",
        "a_boundary": str(a_boundary),
        "total_anomaly": str(total_anomaly),
        "residual_after_measure": str(residual_after_measure),
        "obstruction_after_anomaly": str(obstruction_after_anomaly),
        "obstruction_if_current_conserved": str(obstruction_if_current_conserved),
        "anomaly_cancellation_target_ready": residual_after_measure == 0,
        "nonlinear_current_conservation_derived": False,
        "full_action_variation_closed": False,
        "next_required": "Derive div_J_Z4 = 0 from the nonlinear Z4 gauge current.",
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z4 Anomaly Cancellation Target",
        "",
        f"Status: `{payload['status']}`",
        f"Boundary anomaly: `{payload['a_boundary']}`",
        f"Total anomaly: `{payload['total_anomaly']}`",
        f"Residual after measure closure: `{payload['residual_after_measure']}`",
        f"Obstruction after anomaly closure: `{payload['obstruction_after_anomaly']}`",
        f"Full action variation closed: `{payload['full_action_variation_closed']}`",
        "",
        f"Next required: {payload['next_required']}",
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
