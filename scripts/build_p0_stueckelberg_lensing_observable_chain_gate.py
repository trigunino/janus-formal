from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_stueckelberg_lensing_observable_chain_gate.md")
JSON_PATH = Path("outputs/reports/p0_stueckelberg_lensing_observable_chain_gate.json")


def build_payload() -> dict:
    chain = [
        {
            "name": "null_geodesic_bundle",
            "requirement": "receiver-sector null rays and affine parameter fixed",
            "status": "diagnostic-required",
        },
        {
            "name": "ricci_focusing",
            "requirement": "R_mu_nu k^mu k^nu substituted with Janus sign gate",
            "status": "sign-open",
        },
        {
            "name": "weyl_shear",
            "requirement": "optical shear/tidal Weyl term tracked separately from Ricci source",
            "status": "open",
        },
        {
            "name": "angular_diameter_distance",
            "requirement": "D_A obeys Sachs distance equation with explicit residual columns",
            "status": "diagnostic-required",
        },
        {
            "name": "gauge_observer_source",
            "requirement": "observer tetrad, source redshift, and map convention fixed",
            "status": "open",
        },
    ]
    output_columns = [
        "ricci_null_source",
        "janus_cross_sign_status",
        "weyl_shear_residual",
        "distance_residual",
        "gauge_observer_source_status",
        "qdet_separate",
        "qcross_reduced_sachs",
    ]
    decision = {
        "observable_chain_defined": True,
        "diagnostic_outputs_defined": True,
        "prediction_ready": False,
        "reason": (
            "A lensing observable needs more than Q_cross_sachs: null bundle, Ricci sign, "
            "Weyl/shear, distance, and observer/source gauge must all be explicit. The "
            "chain is defined for diagnostics but remains prediction-blocked."
        ),
    }
    return {
        "artifact": "p0_stueckelberg_lensing_observable_chain_gate",
        "status": "lensing-observable-chain-defined-open",
        "fit_used": False,
        "free_parameters": [],
        "physics_closed": False,
        "prediction_ready": False,
        "chain": chain,
        "output_columns": output_columns,
        "decision": decision,
    }


def render_markdown(payload: dict) -> str:
    decision = payload["decision"]
    lines = [
        "# P0 Stueckelberg Lensing Observable Chain Gate",
        "",
        f"Status: {payload['status']}",
        f"Fit used: {payload['fit_used']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Chain",
    ]
    for row in payload["chain"]:
        lines.append(f"- {row['name']}: {row['requirement']} (status={row['status']})")
    lines.extend(["", "## Output Columns"])
    lines.extend(f"- {item}" for item in payload["output_columns"])
    lines.extend(
        [
            "",
            "## Decision",
            f"Observable chain defined: {decision['observable_chain_defined']}",
            f"Diagnostic outputs defined: {decision['diagnostic_outputs_defined']}",
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
