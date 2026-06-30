from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_stueckelberg_projected_perfect_fluid_extension.md")
JSON_PATH = Path("outputs/reports/p0_stueckelberg_projected_perfect_fluid_extension.json")


def build_payload() -> dict:
    fluid_split = [
        {
            "term": "T^{mu nu}=rho u^mu u^nu",
            "projection": "rho h a",
            "status": "dust-branch-conditional-progress",
        },
        {
            "term": "p h^{mu nu}",
            "projection": "h nabla p + p h nabla h",
            "status": "new-pressure-transport-needed",
        },
        {
            "term": "Pi^{mu nu}",
            "projection": "h nabla_mu Pi^{mu}_{nu}",
            "status": "new-anisotropic-stress-transport-needed",
        },
    ]
    no_absorption_rules = [
        "pressure-gradient terms cannot be absorbed into scalar Q_det",
        "anisotropic Pi divergence cannot be absorbed into scalar Q_cross",
        "lensing normalization cannot be adjusted to hide pressure/Pi transport",
        "dust closure does not imply perfect-fluid closure",
    ]
    decision = {
        "dust_identity_extends_to_full_fluid": False,
        "pressure_transport_required": True,
        "pi_transport_required": True,
        "physics_closed": False,
        "prediction_ready": False,
        "reason": (
            "The projected divergence identity generalizes, but it produces additional "
            "pressure and anisotropic-stress transport terms. These are tensor terms, "
            "not scalar normalization factors, so they require separate Janus transport laws."
        ),
    }
    return {
        "artifact": "p0_stueckelberg_projected_perfect_fluid_extension",
        "status": "perfect-fluid-extension-open",
        "fit_used": False,
        "free_parameters": [],
        "fluid_split": fluid_split,
        "no_absorption_rules": no_absorption_rules,
        "decision": decision,
    }


def render_markdown(payload: dict) -> str:
    decision = payload["decision"]
    lines = [
        "# P0 Stueckelberg Projected Perfect-Fluid Extension",
        "",
        f"Status: {payload['status']}",
        f"Fit used: {payload['fit_used']}",
        f"Physics closed: {decision['physics_closed']}",
        f"Prediction ready: {decision['prediction_ready']}",
        "",
        "## Fluid Split",
    ]
    for row in payload["fluid_split"]:
        lines.append(f"- `{row['term']}` -> `{row['projection']}` ({row['status']})")
    lines.extend(["", "## No Absorption Rules"])
    lines.extend(f"- {item}" for item in payload["no_absorption_rules"])
    lines.extend(
        [
            "",
            "## Decision",
            f"Dust identity extends to full fluid: {decision['dust_identity_extends_to_full_fluid']}",
            f"Pressure transport required: {decision['pressure_transport_required']}",
            f"Pi transport required: {decision['pi_transport_required']}",
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
