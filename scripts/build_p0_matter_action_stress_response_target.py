from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_matter_action_stress_response_target.md")
JSON_PATH = Path("outputs/reports/p0_matter_action_stress_response_target.json")


def build_payload() -> dict:
    matter_branches = [
        {
            "branch": "dust",
            "stress": "T^{mu nu}=rho u^mu u^nu",
            "needed_response": "delta_g rho and delta_g u^mu from constrained particle/dust action",
            "closed": False,
        },
        {
            "branch": "perfect_fluid",
            "stress": "T^{mu nu}=(rho+p)u^mu u^nu+p g^{mu nu}",
            "needed_response": "equation of state plus delta_g p, delta_g rho, delta_g u^mu, delta_g g^{mu nu}",
            "closed": False,
        },
        {
            "branch": "anisotropic_stress",
            "stress": "T^{mu nu}=(rho+p)u^mu u^nu+p h^{mu nu}+Pi^{mu nu}",
            "needed_response": "projector h^{mu nu}, orientation/eigenframe, and delta_g Pi^{mu nu}",
            "closed": False,
        },
    ]
    required_axioms_or_sources = [
        "matter action or variational principle for rho/u/p/Pi",
        "normalization constraint u_mu u^mu=-1 under metric variation",
        "equation of state or closure law for pressure",
        "transport/constitutive law for anisotropic Pi",
        "mirror plus/minus rule using the same phi/L as K and Q_cross",
    ]
    forbidden_shortcuts = [
        "freeze T^{mu nu} and call the measure trace full K",
        "replace pressure or Pi response by scalar Q_cross/Q_det",
        "reuse dust response as perfect-fluid response",
        "reuse FLRW scalar pressure branch for non-comoving tensor stress",
    ]
    return {
        "description": "Matter-action target for deriving delta_g T in the linear I_matter K variation.",
        "status": "matter-action-stress-response-open",
        "matter_branches": matter_branches,
        "required_axioms_or_sources": required_axioms_or_sources,
        "forbidden_shortcuts": forbidden_shortcuts,
        "dust_response_closed": False,
        "dust_metric_stress_response_target_available": True,
        "perfect_fluid_response_closed": False,
        "anisotropic_response_closed": False,
        "same_phi_l_required": True,
        "stress_response_closed": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "delta_g T cannot be closed from the tensor formula alone. It requires a "
            "matter action or constitutive source for each matter branch."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Matter Action Stress Response Target",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Dust response closed: {payload['dust_response_closed']}",
        f"Dust metric stress response target available: {payload['dust_metric_stress_response_target_available']}",
        f"Perfect-fluid response closed: {payload['perfect_fluid_response_closed']}",
        f"Anisotropic response closed: {payload['anisotropic_response_closed']}",
        f"Same phi/L required: {payload['same_phi_l_required']}",
        f"Stress response closed: {payload['stress_response_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Matter Branches",
        "",
    ]
    for row in payload["matter_branches"]:
        lines.append(f"- {row['branch']}: `{row['stress']}`")
        lines.append(f"  - needed response: {row['needed_response']}")
        lines.append(f"  - closed: {row['closed']}")
    lines.extend(["", "## Required Axioms Or Sources", ""])
    lines.extend(f"- {item}" for item in payload["required_axioms_or_sources"])
    lines.extend(["", "## Forbidden Shortcuts", ""])
    lines.extend(f"- {item}" for item in payload["forbidden_shortcuts"])
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
