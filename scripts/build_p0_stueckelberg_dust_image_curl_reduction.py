from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_stueckelberg_dust_image_curl_reduction.md")
JSON_PATH = Path("outputs/reports/p0_stueckelberg_dust_image_curl_reduction.json")


def build_payload() -> dict:
    reductions = [
        {
            "name": "one_dimensional_flow",
            "statement": "on a single dust worldline, antisymmetric two-form curls have no two independent flow directions",
            "effect": "along-flow integrability is automatic once the ODE initial data are fixed",
            "closes": "worldline-only",
        },
        {
            "name": "image_distribution",
            "statement": "a dust congruence is a one-dimensional distribution plus transverse labels",
            "effect": "curl obstruction moves to label-dependence and caustic/crossing consistency",
            "closes": "conditional",
        },
        {
            "name": "transverse_sheets",
            "statement": "different worldlines must define a smooth inverse phi pair and same L field",
            "effect": "full field integrability still needs transverse compatibility",
            "closes": False,
        },
    ]
    remaining_obstructions = [
        "caustics or multi-valued map labels break inverse phi",
        "transverse gradients of initial data can reintroduce curl obstruction",
        "same-L compatibility with Q_cross remains global, not worldline-local",
        "pressure/Pi need transverse transport and are not covered",
    ]
    decision = {
        "dust_worldline_integrability_reduced": True,
        "full_curl_integrability_closed": False,
        "diagnostic_ode_branch_allowed": True,
        "prediction_ready": False,
        "reason": (
            "Restricting to each transported dust worldline turns the map condition into "
            "an ODE and removes local two-form curl obstruction along the flow. The "
            "obstruction survives in transverse label smoothness, mirror invertibility, "
            "and same-L global consistency."
        ),
    }
    return {
        "artifact": "p0_stueckelberg_dust_image_curl_reduction",
        "status": "worldline-curl-reduced-global-open",
        "fit_used": False,
        "free_parameters": [],
        "physics_closed": False,
        "prediction_ready": False,
        "reductions": reductions,
        "remaining_obstructions": remaining_obstructions,
        "decision": decision,
    }


def render_markdown(payload: dict) -> str:
    decision = payload["decision"]
    lines = [
        "# P0 Stueckelberg Dust Image Curl Reduction",
        "",
        f"Status: {payload['status']}",
        f"Fit used: {payload['fit_used']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Reductions",
    ]
    for row in payload["reductions"]:
        lines.append(f"- {row['name']}: {row['statement']}")
        lines.append(f"  - effect: {row['effect']}")
        lines.append(f"  - closes: {row['closes']}")
    lines.extend(["", "## Remaining Obstructions"])
    lines.extend(f"- {item}" for item in payload["remaining_obstructions"])
    lines.extend(
        [
            "",
            "## Decision",
            f"Dust worldline integrability reduced: {decision['dust_worldline_integrability_reduced']}",
            f"Full curl integrability closed: {decision['full_curl_integrability_closed']}",
            f"Diagnostic ODE branch allowed: {decision['diagnostic_ode_branch_allowed']}",
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
