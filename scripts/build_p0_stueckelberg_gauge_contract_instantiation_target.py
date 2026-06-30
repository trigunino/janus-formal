from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_stueckelberg_gauge_contract_instantiation_target.md")
JSON_PATH = Path("outputs/reports/p0_stueckelberg_gauge_contract_instantiation_target.json")


def build_payload() -> dict:
    fields = [
        {
            "name": "observer_tetrad_id",
            "type": "declared-frame",
            "required": True,
        },
        {
            "name": "source_four_velocity",
            "type": "receiver-metric-vector",
            "required": True,
        },
        {
            "name": "photon_wavevector",
            "type": "null-vector-normalized-at-observer",
            "required": True,
        },
        {
            "name": "phi_l_branch_id",
            "type": "transport-convention-id",
            "required": True,
        },
        {
            "name": "affine_normalization",
            "type": "E_obs=-u_obs.k",
            "required": True,
        },
    ]
    validations = [
        "k.k=0 in receiver metric",
        "observer tetrad is orthonormal",
        "1+z computed from source/observer contractions, not fitted",
        "phi/L branch matches transported stress and Q_cross branch",
        "affine normalization is fixed before Sachs integration",
    ]
    decision = {
        "instantiation_target_defined": True,
        "contract_fields_complete": True,
        "instantiated_with_data": False,
        "prediction_ready": False,
        "reason": (
            "The gauge contract is now executable as a schema. It still needs actual "
            "ray/source data from the perturbed metric solver before survey prediction."
        ),
    }
    return {
        "artifact": "p0_stueckelberg_gauge_contract_instantiation_target",
        "status": "gauge-contract-instantiation-target-open",
        "fit_used": False,
        "free_parameters": [],
        "physics_closed": False,
        "prediction_ready": False,
        "fields": fields,
        "validations": validations,
        "decision": decision,
    }


def render_markdown(payload: dict) -> str:
    decision = payload["decision"]
    lines = [
        "# P0 Stueckelberg Gauge Contract Instantiation Target",
        "",
        f"Status: {payload['status']}",
        f"Fit used: {payload['fit_used']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Fields",
    ]
    for row in payload["fields"]:
        lines.append(f"- {row['name']}: {row['type']} (required={row['required']})")
    lines.extend(["", "## Validations"])
    lines.extend(f"- {item}" for item in payload["validations"])
    lines.extend(
        [
            "",
            "## Decision",
            f"Instantiation target defined: {decision['instantiation_target_defined']}",
            f"Contract fields complete: {decision['contract_fields_complete']}",
            f"Instantiated with data: {decision['instantiated_with_data']}",
            f"Prediction ready: {decision['prediction_ready']}",
            f"Reason: {decision['reason']}",
            "",
        ]
    )
    return "\n".join(lines)


def write_reports(report_path: Path = REPORT_PATH, json_path: Path = JSON_PATH) -> dict:
    payload = build_payload()
    report_path.parent.mkdir(parents=True, exist_ok=True)
    report_path.write_text(render_markdown(payload), encoding="utf-8")
    json_path.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    return payload


if __name__ == "__main__":
    write_reports()
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {JSON_PATH}")
