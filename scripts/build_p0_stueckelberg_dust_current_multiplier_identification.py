from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_stueckelberg_dust_current_multiplier_identification.md")
JSON_PATH = Path("outputs/reports/p0_stueckelberg_dust_current_multiplier_identification.json")


def build_payload() -> dict:
    identifications = [
        {
            "sector": "plus",
            "new_multiplier": "lambda_plus_mu",
            "candidate_existing_object": "rho_minus_to_plus u_-to+_mu",
            "variation_shape": "rho_minus_to_plus u_-to+_mu u_-to+^nu D_plus_nu u_-to+^mu",
            "problem": "contraction with u_mu kills normalized geodesic acceleration because u_mu a^mu=0",
            "works_as_vector_multiplier": False,
        },
        {
            "sector": "minus",
            "new_multiplier": "lambda_minus_a",
            "candidate_existing_object": "rho_plus_to_minus u_+to-_a",
            "variation_shape": "rho_plus_to_minus u_+to-_a u_+to-^b D_minus_b u_+to-^a",
            "problem": "same orthogonality obstruction in the mirror sector",
            "works_as_vector_multiplier": False,
        },
    ]
    needed_projection = [
        "A useful multiplier must live in the transverse projector h_mu_nu = g_mu_nu + u_mu u_nu.",
        "Dust alone supplies u_mu and rho, but no preferred transverse vector.",
        "Therefore dust current alone cannot enforce all transverse components of C u u = 0.",
        "A full vector multiplier would be new unless produced by phi/L variation or boundary data.",
    ]
    partial_progress = [
        "The weak equation target is still correct: C u u = 0.",
        "The naive lambda = rho u identification fails cleanly and explains why.",
        "Closure must come from variation of the map variables themselves, not from the dust current alone.",
    ]
    decision = {
        "dust_current_identification_works": False,
        "orthogonality_obstruction_found": True,
        "transverse_multiplier_needed": True,
        "new_axiom_if_transverse_multiplier_added": True,
        "accepted_as_final_closure": False,
        "reason": (
            "The existing dust current is parallel to u. For normalized dust, acceleration "
            "is transverse, so rho u_mu a^mu vanishes and cannot enforce the vector "
            "condition a^mu=0. The missing multiplier must be transverse or must arise "
            "directly from phi/L Euler-Lagrange variation."
        ),
    }
    return {
        "artifact": "p0_stueckelberg_dust_current_multiplier_identification",
        "status": "dust-current-identification-rejected",
        "fit_used": False,
        "free_parameters": [],
        "physics_closed": False,
        "prediction_ready": False,
        "identifications": identifications,
        "needed_projection": needed_projection,
        "partial_progress": partial_progress,
        "decision": decision,
        "next_step": (
            "Derive the transverse projector source from phi/L variation; if none appears, "
            "the weak congruence constraint is an extra axiom rather than dust-derived."
        ),
    }


def render_markdown(payload: dict) -> str:
    decision = payload["decision"]
    lines = [
        "# P0 Dust Current Multiplier Identification",
        "",
        f"Status: {payload['status']}",
        f"Fit used: {payload['fit_used']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Identification Tests",
    ]
    for row in payload["identifications"]:
        lines.append(f"- {row['sector']}: `{row['new_multiplier']} -> {row['candidate_existing_object']}`")
        lines.append(f"  - variation shape: `{row['variation_shape']}`")
        lines.append(f"  - works as vector multiplier: {row['works_as_vector_multiplier']}")
        lines.append(f"  - problem: {row['problem']}")
    lines.extend(["", "## Needed Projection"])
    lines.extend(f"- {item}" for item in payload["needed_projection"])
    lines.extend(["", "## Partial Progress"])
    lines.extend(f"- {item}" for item in payload["partial_progress"])
    lines.extend(
        [
            "",
            "## Decision",
            f"Dust current identification works: {decision['dust_current_identification_works']}",
            f"Orthogonality obstruction found: {decision['orthogonality_obstruction_found']}",
            f"Transverse multiplier needed: {decision['transverse_multiplier_needed']}",
            f"New axiom if transverse multiplier added: {decision['new_axiom_if_transverse_multiplier_added']}",
            f"Accepted as final closure: {decision['accepted_as_final_closure']}",
            f"Reason: {decision['reason']}",
            "",
            f"Next step: {payload['next_step']}",
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
