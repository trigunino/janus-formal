from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_linear_imatter_stress_response_target.md")
JSON_PATH = Path("outputs/reports/p0_linear_imatter_stress_response_target.json")


def build_payload() -> dict:
    response_terms = [
        {
            "term": "measure_trace",
            "formula": "-1/2 g_plus_{mu nu} Phi",
            "status": "closed-algebraic",
        },
        {
            "term": "same_sector_stress_response",
            "formula": "delta_g T_plus^{alpha beta} from the matter action/constitutive law",
            "status": "required-open",
        },
        {
            "term": "solder_metric_response",
            "formula": "delta_g L_mu^a subject to Lorentz/tetrad compatibility",
            "status": "required-open",
        },
        {
            "term": "pulled_stress_response",
            "formula": "delta_g (L T_minus L^T)_{alpha beta}, including pullback/Jacobian conventions",
            "status": "required-open",
        },
        {
            "term": "mirror_minus_response",
            "formula": "same decomposition with plus/minus exchanged and inverse pullback",
            "status": "required-open",
        },
    ]
    closure_rules = [
        "do not identify measure_trace with K_plus/K_minus",
        "do not absorb delta_g T or delta_g L into scalar Q_cross/Q_det",
        "perfect-fluid pressure and anisotropic Pi require their own transport laws",
        "prediction is forbidden until both plus and minus metric responses are substituted in R_plus/R_minus",
    ]
    return {
        "description": "Full stress-response target needed to turn the linear I_matter variation into K_plus/K_minus.",
        "status": "stress-response-target-open",
        "response_terms": response_terms,
        "closure_rules": closure_rules,
        "measure_trace_closed": True,
        "same_sector_stress_response_closed": False,
        "solder_metric_response_closed": False,
        "pulled_stress_response_closed": False,
        "mirror_response_closed": False,
        "matter_action_stress_response_target_available": True,
        "full_k_variation_closed": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "The missing object is now localized: a variational stress response for matter, "
            "solder field, and pullback data. The closed trace term alone is not a physical K tensor."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Linear I_matter Stress Response Target",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Measure trace closed: {payload['measure_trace_closed']}",
        f"Same-sector stress response closed: {payload['same_sector_stress_response_closed']}",
        f"Solder metric response closed: {payload['solder_metric_response_closed']}",
        f"Pulled stress response closed: {payload['pulled_stress_response_closed']}",
        f"Mirror response closed: {payload['mirror_response_closed']}",
        f"Matter action stress response target available: {payload['matter_action_stress_response_target_available']}",
        f"Full K variation closed: {payload['full_k_variation_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Response Terms",
        "",
    ]
    for row in payload["response_terms"]:
        lines.append(f"- {row['term']}: `{row['formula']}` ({row['status']})")
    lines.extend(["", "## Closure Rules", ""])
    lines.extend(f"- {rule}" for rule in payload["closure_rules"])
    lines.extend(["", f"Verdict: {payload['verdict']}", ""])
    return "\n".join(lines)


def write_reports(report_path: Path = REPORT_PATH, json_path: Path = JSON_PATH) -> dict:
    report_path.parent.mkdir(parents=True, exist_ok=True)
    json_path.parent.mkdir(parents=True, exist_ok=True)
    payload = build_payload()
    json_path.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    report_path.write_text(render_markdown(payload), encoding="utf-8")
    return payload


def main() -> None:
    write_reports()
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {JSON_PATH}")


if __name__ == "__main__":
    main()
