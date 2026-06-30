from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_stueckelberg_observer_source_gauge_contract.md")
JSON_PATH = Path("outputs/reports/p0_stueckelberg_observer_source_gauge_contract.json")


def build_payload() -> dict:
    contract = [
        {
            "name": "observer_tetrad",
            "requirement": "declare positive-sector observer tetrad e_obs and photon energy normalization E_obs=-u_obs.k",
            "status": "required",
        },
        {
            "name": "source_redshift",
            "requirement": "compute 1+z=(u_src.k_src)/(u_obs.k_obs) in the same receiver metric",
            "status": "required",
        },
        {
            "name": "affine_scale",
            "requirement": "fix affine lambda by observer normalization before integrating Sachs equations",
            "status": "required",
        },
        {
            "name": "map_convention",
            "requirement": "record phi/L branch used for transported source stress and Q_cross",
            "status": "required",
        },
    ]
    forbidden = [
        "no fitted redshift remapping",
        "no observer calibration multiplier hidden in distance",
        "no switching tetrads between stress transport and optical projection",
        "no survey comparison without all contract fields present",
    ]
    decision = {
        "gauge_contract_defined": True,
        "survey_ready": False,
        "prediction_ready": False,
        "reason": (
            "Observer/source gauge is now a concrete data contract. It does not close "
            "survey lensing, but it prevents gauge choices from becoming hidden fit "
            "parameters."
        ),
    }
    return {
        "artifact": "p0_stueckelberg_observer_source_gauge_contract",
        "status": "observer-source-gauge-contract-defined-open",
        "fit_used": False,
        "free_parameters": [],
        "physics_closed": False,
        "prediction_ready": False,
        "contract": contract,
        "forbidden": forbidden,
        "decision": decision,
    }


def render_markdown(payload: dict) -> str:
    decision = payload["decision"]
    lines = [
        "# P0 Stueckelberg Observer Source Gauge Contract",
        "",
        f"Status: {payload['status']}",
        f"Fit used: {payload['fit_used']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Contract",
    ]
    for row in payload["contract"]:
        lines.append(f"- {row['name']}: {row['requirement']} (status={row['status']})")
    lines.extend(["", "## Forbidden"])
    lines.extend(f"- {item}" for item in payload["forbidden"])
    lines.extend(
        [
            "",
            "## Decision",
            f"Gauge contract defined: {decision['gauge_contract_defined']}",
            f"Survey ready: {decision['survey_ready']}",
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
