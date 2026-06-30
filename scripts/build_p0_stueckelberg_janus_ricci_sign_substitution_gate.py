from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_stueckelberg_janus_ricci_sign_substitution_gate.md")
JSON_PATH = Path("outputs/reports/p0_stueckelberg_janus_ricci_sign_substitution_gate.json")


def build_payload() -> dict:
    substitutions = [
        {
            "sector": "plus_ray_plus_source",
            "form": "R_plus_mu_nu k^mu k^nu <- +C_plus G_plus[T_plus]_{mu nu} k^mu k^nu",
            "sign_status": "standard-attractive-branch",
        },
        {
            "sector": "plus_ray_minus_source",
            "form": "R_plus_mu_nu k^mu k^nu <- s_cross C_cross G_cross[T_minus_to_plus]_{mu nu} k^mu k^nu",
            "sign_status": "must-be-derived-from-Janus-field-equation",
        },
        {
            "sector": "minus_ray_plus_source",
            "form": "R_minus_ab ell^a ell^b <- mirror(s_cross) C_cross G_cross[T_plus_to_minus]_{ab} ell^a ell^b",
            "sign_status": "mirror-required",
        },
    ]
    sign_rules = [
        "s_cross belongs in the Ricci/source substitution, not in optical post-normalization",
        "s_cross must be fixed by Janus field equations or cited source convention",
        "Q_det/Jacobian factors do not determine attraction/repulsion sign",
        "mirror signs must be inverse-consistent across plus/minus equations",
    ]
    decision = {
        "sign_location_fixed": True,
        "janus_cross_sign_value_derived": False,
        "can_use_reduced_sachs_diagnostic": True,
        "can_claim_lensing_prediction": False,
        "prediction_ready": False,
        "reason": (
            "The sign problem is now localized: it must enter through the Janus "
            "Ricci/source substitution coefficient s_cross. It cannot be hidden in "
            "Q_cross, Q_det, or observational normalization."
        ),
    }
    return {
        "artifact": "p0_stueckelberg_janus_ricci_sign_substitution_gate",
        "status": "ricci-sign-location-fixed-value-open",
        "fit_used": False,
        "free_parameters": [],
        "physics_closed": False,
        "prediction_ready": False,
        "substitutions": substitutions,
        "sign_rules": sign_rules,
        "decision": decision,
    }


def render_markdown(payload: dict) -> str:
    decision = payload["decision"]
    lines = [
        "# P0 Stueckelberg Janus Ricci Sign Substitution Gate",
        "",
        f"Status: {payload['status']}",
        f"Fit used: {payload['fit_used']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Substitutions",
    ]
    for row in payload["substitutions"]:
        lines.append(f"- {row['sector']}: `{row['form']}`")
        lines.append(f"  - sign status: {row['sign_status']}")
    lines.extend(["", "## Sign Rules"])
    lines.extend(f"- {item}" for item in payload["sign_rules"])
    lines.extend(
        [
            "",
            "## Decision",
            f"Sign location fixed: {decision['sign_location_fixed']}",
            f"Janus cross sign value derived: {decision['janus_cross_sign_value_derived']}",
            f"Can use reduced Sachs diagnostic: {decision['can_use_reduced_sachs_diagnostic']}",
            f"Can claim lensing prediction: {decision['can_claim_lensing_prediction']}",
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
