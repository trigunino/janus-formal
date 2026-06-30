from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_stueckelberg_shear_distance_gauge_closure_gate.md")
JSON_PATH = Path("outputs/reports/p0_stueckelberg_shear_distance_gauge_closure_gate.json")


def build_payload() -> dict:
    branches = [
        {
            "name": "flrw_background_distance",
            "equation": "D_A = D_M/(1+z) with M18 open marker distance",
            "status": "accepted-working",
            "scope": "homogeneous positive-photon background",
        },
        {
            "name": "ricci_reduced_sachs_source",
            "equation": "R_kk diagnostic source uses s_cross=-1 for opposite-sign weak-field source",
            "status": "accepted-working-diagnostic",
            "scope": "reduced Sachs scalar source",
        },
        {
            "name": "weyl_shear",
            "equation": "d sigma/dlambda uses Weyl/tidal screen projection",
            "status": "open",
            "scope": "perturbed lensing observable",
        },
        {
            "name": "observer_source_gauge",
            "equation": "observer tetrad, source redshift, affine normalization fixed before comparison",
            "status": "open",
            "scope": "survey observable",
        },
    ]
    output_policy = [
        "report Ricci, Weyl/shear, distance and gauge residuals as separate columns",
        "do not promote FLRW distance closure to perturbed lensing closure",
        "do not infer shear-screen relation from standard GR if Janus tensor route changes it",
        "do not fit gauge/source-redshift corrections",
    ]
    decision = {
        "background_distance_closed_for_diagnostic": True,
        "reduced_ricci_sign_closed_for_diagnostic": True,
        "weyl_shear_closed": False,
        "observer_source_gauge_closed": False,
        "prediction_ready": False,
        "reason": (
            "The M18 background distance and M15/M30 weak-field cross sign are usable "
            "for reduced diagnostics. Full lensing remains open because Weyl/shear and "
            "observer/source gauge are perturbed-observable gates."
        ),
    }
    return {
        "artifact": "p0_stueckelberg_shear_distance_gauge_closure_gate",
        "status": "distance-sign-diagnostic-closed-shear-gauge-open",
        "fit_used": False,
        "free_parameters": [],
        "physics_closed": False,
        "prediction_ready": False,
        "branches": branches,
        "output_policy": output_policy,
        "decision": decision,
    }


def render_markdown(payload: dict) -> str:
    decision = payload["decision"]
    lines = [
        "# P0 Stueckelberg Shear Distance Gauge Closure Gate",
        "",
        f"Status: {payload['status']}",
        f"Fit used: {payload['fit_used']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Branches",
    ]
    for row in payload["branches"]:
        lines.append(f"- {row['name']}: `{row['equation']}`")
        lines.append(f"  - status: {row['status']}")
        lines.append(f"  - scope: {row['scope']}")
    lines.extend(["", "## Output Policy"])
    lines.extend(f"- {item}" for item in payload["output_policy"])
    lines.extend(
        [
            "",
            "## Decision",
            f"Background distance closed for diagnostic: {decision['background_distance_closed_for_diagnostic']}",
            f"Reduced Ricci sign closed for diagnostic: {decision['reduced_ricci_sign_closed_for_diagnostic']}",
            f"Weyl shear closed: {decision['weyl_shear_closed']}",
            f"Observer source gauge closed: {decision['observer_source_gauge_closed']}",
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
