from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_stueckelberg_transverse_label_caustic_gate.md")
JSON_PATH = Path("outputs/reports/p0_stueckelberg_transverse_label_caustic_gate.json")


def build_payload() -> dict:
    gates = [
        {
            "name": "transverse_jacobian_nonzero",
            "condition": "det(partial X_to^i / partial q^A)_transverse != 0 on the dust support",
            "role": "prevents neighbouring dust labels from collapsing into a caustic",
            "status": "required-not-proved",
        },
        {
            "name": "single_valued_phi",
            "condition": "each source label q maps to one receiver event before shell crossing",
            "role": "keeps phi a map, not a multi-stream relation",
            "status": "required-not-proved",
        },
        {
            "name": "mirror_inverse_domain",
            "condition": "phi_plus_to_minus(phi_minus_to_plus(q)) = q on the supported domain",
            "role": "ensures plus/minus residuals are inverse mirrors",
            "status": "required-not-proved",
        },
        {
            "name": "same_l_smoothness",
            "condition": "L(q,t) is smooth across transverse labels and remains Lorentz-compatible",
            "role": "prevents worldline-local L choices from becoming incompatible globally",
            "status": "required-not-proved",
        },
    ]
    diagnostic_rules = [
        "diagnostic ODE branch is valid only before caustic/shell crossing",
        "when transverse Jacobian approaches zero, stop treating phi as a diffeomorphism",
        "multi-stream dust requires a kinetic or sheet-summed extension, not current closure",
        "do not use caustic smoothing as a fit parameter",
    ]
    decision = {
        "worldline_branch_domain_limited": True,
        "caustic_free_condition_required": True,
        "full_global_closure": False,
        "diagnostic_allowed_until_caustic": True,
        "prediction_ready": False,
        "reason": (
            "The dust ODE reduction is valid only on a caustic-free congruence patch. "
            "Global closure needs a nonzero transverse Jacobian, single-valued phi, "
            "mirror inverse consistency, and smooth same-L transport."
        ),
    }
    return {
        "artifact": "p0_stueckelberg_transverse_label_caustic_gate",
        "status": "caustic-free-label-gate-open",
        "fit_used": False,
        "free_parameters": [],
        "physics_closed": False,
        "prediction_ready": False,
        "gates": gates,
        "diagnostic_rules": diagnostic_rules,
        "decision": decision,
    }


def render_markdown(payload: dict) -> str:
    decision = payload["decision"]
    lines = [
        "# P0 Stueckelberg Transverse Label Caustic Gate",
        "",
        f"Status: {payload['status']}",
        f"Fit used: {payload['fit_used']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Gates",
    ]
    for row in payload["gates"]:
        lines.append(f"- {row['name']}: `{row['condition']}`")
        lines.append(f"  - role: {row['role']}")
        lines.append(f"  - status: {row['status']}")
    lines.extend(["", "## Diagnostic Rules"])
    lines.extend(f"- {item}" for item in payload["diagnostic_rules"])
    lines.extend(
        [
            "",
            "## Decision",
            f"Worldline branch domain limited: {decision['worldline_branch_domain_limited']}",
            f"Caustic-free condition required: {decision['caustic_free_condition_required']}",
            f"Full global closure: {decision['full_global_closure']}",
            f"Diagnostic allowed until caustic: {decision['diagnostic_allowed_until_caustic']}",
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
