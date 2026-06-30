from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_stueckelberg_metric_potential_closure_contract.md")
JSON_PATH = Path("outputs/reports/p0_stueckelberg_metric_potential_closure_contract.json")


def build_payload() -> dict:
    conditions = [
        {
            "id": "linearized_field_equation",
            "required": "derive delta G_plus[h_plus] = chi delta S_plus from Janus sources",
            "closed": False,
        },
        {
            "id": "gauge_lock",
            "required": "declare weak-field gauge and metric potentials h00=-2 Phi, hij=2 Psi delta_ij or explicit alternative",
            "closed": False,
        },
        {
            "id": "slip_relation",
            "required": "derive Phi_lens_plus=(Phi+Psi) or its Janus replacement from anisotropic stress/source equations",
            "closed": False,
        },
        {
            "id": "source_identity",
            "required": "prove Delta Phi_lens_plus equals declared rho_eff_plus without fitted lensing amplitude",
            "closed": False,
        },
    ]
    forbidden_shortcuts = [
        "do not identify the PM Poisson potential with h_plus unless gauge and slip are derived",
        "do not tune Phi_lens_plus to shear, sigma8 or S8 data",
        "do not absorb missing Weyl terms into Q_cross or Q_det",
        "do not use a_minus/a_plus as potential or lensing amplitude",
    ]
    decision = {
        "closure_contract_defined": True,
        "all_conditions_closed": all(row["closed"] for row in conditions),
        "poisson_diagnostic_promoted_to_metric": False,
        "prediction_ready": False,
        "reason": (
            "The weak-field Poisson chain is now separated from the metric-potential "
            "closure proof. Promotion requires field equation, gauge, slip and source "
            "identity closure from Janus equations."
        ),
    }
    return {
        "artifact": "p0_stueckelberg_metric_potential_closure_contract",
        "status": "metric-potential-closure-open",
        "fit_used": False,
        "free_parameters": [],
        "physics_closed": False,
        "prediction_ready": False,
        "conditions": conditions,
        "forbidden_shortcuts": forbidden_shortcuts,
        "decision": decision,
    }


def render_markdown(payload: dict) -> str:
    decision = payload["decision"]
    lines = [
        "# P0 Stueckelberg Metric Potential Closure Contract",
        "",
        f"Status: {payload['status']}",
        f"Fit used: {payload['fit_used']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Conditions",
    ]
    for row in payload["conditions"]:
        lines.append(f"- {row['id']}: {row['required']} (closed={row['closed']})")
    lines.extend(["", "## Forbidden Shortcuts"])
    lines.extend(f"- {item}" for item in payload["forbidden_shortcuts"])
    lines.extend(
        [
            "",
            "## Decision",
            f"Closure contract defined: {decision['closure_contract_defined']}",
            f"All conditions closed: {decision['all_conditions_closed']}",
            f"Poisson diagnostic promoted to metric: {decision['poisson_diagnostic_promoted_to_metric']}",
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
