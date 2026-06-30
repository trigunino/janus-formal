from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_dust_metric_stress_response_target.md")
JSON_PATH = Path("outputs/reports/p0_dust_metric_stress_response_target.json")


def build_payload() -> dict:
    identities = [
        {
            "name": "dust_stress",
            "formula": "T^{mu nu}=rho u^mu u^nu",
            "status": "defined",
        },
        {
            "name": "stress_variation_chain_rule",
            "formula": "delta_g T^{mu nu}=u^mu u^nu delta_g rho + rho u^nu delta_g u^mu + rho u^mu delta_g u^nu",
            "status": "closed-algebraic",
        },
        {
            "name": "normalization_constraint",
            "formula": "delta_g(g_{mu nu}u^mu u^nu)=0",
            "status": "closed-algebraic",
        },
        {
            "name": "normalization_projection",
            "formula": "u_mu delta_g u^mu = -1/2 u^mu u^nu delta g_{mu nu}",
            "status": "closed-algebraic",
        },
        {
            "name": "density_response",
            "formula": "delta_g rho must come from dust current measure or pulled dust action",
            "status": "open-source-required",
        },
        {
            "name": "transverse_velocity_response",
            "formula": "h^mu_nu delta_g u^nu depends on particle-label/trajectory variation",
            "status": "open-source-required",
        },
    ]
    closure_requirements = [
        "choose covariant dust action or fixed-current convention",
        "derive delta_g rho from conserved current density",
        "derive or gauge-fix transverse delta_g u consistently",
        "apply the same rule to transported/pulled dust in K_plus/K_minus",
    ]
    return {
        "description": "Dust-only metric stress response target for delta_g T in the linear I_matter branch.",
        "status": "dust-chain-rule-closed-action-response-open",
        "identities": identities,
        "dust_chain_rule_closed": True,
        "normalization_projection_closed": True,
        "fixed_current_density_response_available": True,
        "fixed_pullback_delta_t_branch_available": True,
        "density_response_closed": False,
        "transverse_velocity_response_closed": False,
        "pulled_dust_response_closed": False,
        "full_dust_delta_g_t_closed": False,
        "physics_closed": False,
        "prediction_ready": False,
        "closure_requirements": closure_requirements,
        "verdict": (
            "The algebraic dust variation is fixed, but full delta_g T is not: rho and "
            "transverse velocity response must be derived from the dust action/convention."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Dust Metric Stress Response Target",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Dust chain rule closed: {payload['dust_chain_rule_closed']}",
        f"Normalization projection closed: {payload['normalization_projection_closed']}",
        f"Fixed current density response available: {payload['fixed_current_density_response_available']}",
        f"Fixed pullback delta T branch available: {payload['fixed_pullback_delta_t_branch_available']}",
        f"Density response closed: {payload['density_response_closed']}",
        f"Transverse velocity response closed: {payload['transverse_velocity_response_closed']}",
        f"Pulled dust response closed: {payload['pulled_dust_response_closed']}",
        f"Full dust delta_g T closed: {payload['full_dust_delta_g_t_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Identities",
        "",
    ]
    for row in payload["identities"]:
        lines.append(f"- {row['name']}: `{row['formula']}` ({row['status']})")
    lines.extend(["", "## Closure Requirements", ""])
    lines.extend(f"- {item}" for item in payload["closure_requirements"])
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
