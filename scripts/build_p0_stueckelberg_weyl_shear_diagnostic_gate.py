from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_stueckelberg_weyl_shear_diagnostic_gate.md")
JSON_PATH = Path("outputs/reports/p0_stueckelberg_weyl_shear_diagnostic_gate.json")


def build_payload() -> dict:
    equations = [
        {
            "name": "optical_shear",
            "equation": "d sigma/dlambda + 2 theta sigma = -C_{mu alpha nu beta} m^mu k^alpha m^nu k^beta",
            "status": "standard-optical-identity",
        },
        {
            "name": "janus_weyl_source",
            "equation": "C_plus[k,m,k,m] must be computed from receiver metric perturbation, not from Q_cross",
            "status": "diagnostic-target",
        },
        {
            "name": "ricci_weyl_separation",
            "equation": "Ricci focusing uses R_kk; shear uses Weyl screen contraction",
            "status": "enforced",
        },
    ]
    blocked_shortcuts = [
        "do not import standard E-mode shear as proof if Janus tensor route changes screen geometry",
        "do not absorb Weyl/shear residual into Q_cross_sachs",
        "do not fit a shear calibration multiplier",
        "do not mix Ricci negative-lensing sign with Weyl tidal sign",
    ]
    decision = {
        "weyl_shear_equation_defined": True,
        "ricci_weyl_separated": True,
        "weyl_source_derived_from_janus_metric": False,
        "prediction_ready": False,
        "reason": (
            "The shear gate is now explicit: compute Weyl screen contraction separately "
            "from Ricci focusing. This is a diagnostic target until the Janus perturbed "
            "receiver metric supplies C[k,m,k,m]."
        ),
    }
    return {
        "artifact": "p0_stueckelberg_weyl_shear_diagnostic_gate",
        "status": "weyl-shear-diagnostic-defined-open",
        "fit_used": False,
        "free_parameters": [],
        "physics_closed": False,
        "prediction_ready": False,
        "equations": equations,
        "blocked_shortcuts": blocked_shortcuts,
        "decision": decision,
    }


def render_markdown(payload: dict) -> str:
    decision = payload["decision"]
    lines = [
        "# P0 Stueckelberg Weyl Shear Diagnostic Gate",
        "",
        f"Status: {payload['status']}",
        f"Fit used: {payload['fit_used']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Equations",
    ]
    for row in payload["equations"]:
        lines.append(f"- {row['name']}: `{row['equation']}` (status={row['status']})")
    lines.extend(["", "## Blocked Shortcuts"])
    lines.extend(f"- {item}" for item in payload["blocked_shortcuts"])
    lines.extend(
        [
            "",
            "## Decision",
            f"Weyl shear equation defined: {decision['weyl_shear_equation_defined']}",
            f"Ricci Weyl separated: {decision['ricci_weyl_separated']}",
            f"Weyl source derived from Janus metric: {decision['weyl_source_derived_from_janus_metric']}",
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
