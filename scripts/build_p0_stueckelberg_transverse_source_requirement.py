from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_stueckelberg_transverse_source_requirement.md")
JSON_PATH = Path("outputs/reports/p0_stueckelberg_transverse_source_requirement.json")


def build_payload() -> dict:
    candidate_sources = [
        {
            "name": "phi_gradient_source",
            "form": "h^mu_nu delta S_matter / delta phi^A partial^nu phi^A",
            "can_be_existing": True,
            "obligation": "must reduce to projected C u u without adding transverse data",
        },
        {
            "name": "lorentz_frame_source",
            "form": "h^mu_nu delta S_matter / delta L^{IJ} D^nu L_{IJ}",
            "can_be_existing": True,
            "obligation": "must use same L as K and Q_cross",
        },
        {
            "name": "external_transverse_multiplier",
            "form": "lambda_perp_mu h^mu_nu a^nu",
            "can_be_existing": False,
            "obligation": "reject unless source-derived",
        },
    ]
    required_identity = {
        "target": "h^mu_nu E_map^nu = rho_to h^mu_nu C^nu_{alpha beta} u^alpha u^beta",
        "meaning": "map variation supplies exactly the transverse projected acceleration source",
        "status": "required-not-proved",
    }
    implications = [
        "This is stricter than imposing C u u = 0 by hand.",
        "It explains why dust current alone failed: the source must be transverse.",
        "It keeps the weak condition compatible with non-isometric two-metric geometry.",
        "It remains blocked until E_phi/E_L are expanded from the actual pulled matter action.",
    ]
    decision = {
        "best_no_new_field_route": "projected phi/L Euler-Lagrange source",
        "external_multiplier_rejected": True,
        "source_derived": False,
        "physics_closed": False,
        "prediction_ready": False,
        "reason": (
            "The only non-axiomatic route left is to show that the transverse projector "
            "of the phi/L matter variation equals the projected connection residual. "
            "Any independent transverse multiplier is a new field."
        ),
    }
    return {
        "artifact": "p0_stueckelberg_transverse_source_requirement",
        "status": "best-route-identified-not-proved",
        "fit_used": False,
        "free_parameters": [],
        "candidate_sources": candidate_sources,
        "required_identity": required_identity,
        "implications": implications,
        "decision": decision,
    }


def render_markdown(payload: dict) -> str:
    decision = payload["decision"]
    identity = payload["required_identity"]
    lines = [
        "# P0 Stueckelberg Transverse Source Requirement",
        "",
        f"Status: {payload['status']}",
        f"Fit used: {payload['fit_used']}",
        f"Source derived: {decision['source_derived']}",
        f"Physics closed: {decision['physics_closed']}",
        f"Prediction ready: {decision['prediction_ready']}",
        "",
        "## Candidate Sources",
    ]
    for row in payload["candidate_sources"]:
        lines.append(f"- {row['name']}: `{row['form']}`")
        lines.append(f"  - can be existing: {row['can_be_existing']}")
        lines.append(f"  - obligation: {row['obligation']}")
    lines.extend(
        [
            "",
            "## Required Identity",
            f"Target: `{identity['target']}`",
            f"Meaning: {identity['meaning']}",
            f"Status: {identity['status']}",
            "",
            "## Implications",
        ]
    )
    lines.extend(f"- {item}" for item in payload["implications"])
    lines.extend(
        [
            "",
            "## Decision",
            f"Best no-new-field route: {decision['best_no_new_field_route']}",
            f"External multiplier rejected: {decision['external_multiplier_rejected']}",
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
