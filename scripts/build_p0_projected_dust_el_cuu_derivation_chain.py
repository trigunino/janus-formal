from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_projected_dust_el_cuu_derivation_chain.md")
JSON_PATH = Path("outputs/reports/p0_projected_dust_el_cuu_derivation_chain.json")


def build_payload() -> dict:
    derivation_steps = [
        {
            "step": "el_variation",
            "formula": "delta S_dust = -int sqrt|g| (nabla_mu T^mu_nu) xi^nu",
            "result": "E_nu = -nabla_mu T^mu_nu",
            "closed": True,
        },
        {
            "step": "dust_divergence_split",
            "formula": "nabla_mu(rho u^mu u_nu)=u_nu nabla_mu(rho u^mu)+rho u^mu nabla_mu u_nu",
            "result": "separates longitudinal continuity from transverse force",
            "closed": True,
        },
        {
            "step": "transverse_projection",
            "formula": "h^nu_sigma u_nu nabla_mu(rho u^mu)=0",
            "result": "h^nu_sigma E_nu = -rho h^nu_sigma u^mu nabla_mu u_nu",
            "closed": True,
        },
        {
            "step": "transported_acceleration_split",
            "formula": "u_to^alpha D_receiver_alpha u_to^mu = L(a_source)^mu + C^mu_alpha_beta u_to^alpha u_to^beta",
            "result": "source-geodesic and D_L rows leave the projected Cuu force",
            "closed": True,
        },
        {
            "step": "projected_cuu_identity",
            "formula": "h E_{phi/L} = rho h C(u_to,u_to)",
            "result": "single cross-dust identity follows; mirror/dynamic phi/L remain open",
            "closed": "single-cross-dust",
        },
    ]
    remaining_conditions = [
        "measure row closed for single cross dust: D_receiver(B_4vol rho_to u_to)=0",
        "dynamic phi/L row: Janus action selects the same map, not only declared pullback",
        "mirror row: plus/minus identities follow from one inverse phi/L",
        "sign convention fixed between E_nu and residual force",
        "pressure/Pi excluded or separately transported",
    ]
    return {
        "description": "Projected dust Euler-Lagrange derivation chain toward hE=rho hCuu.",
        "status": "partial-derivation-chain-open",
        "derivation_steps": derivation_steps,
        "remaining_conditions": remaining_conditions,
        "standard_dust_projection_derived": True,
        "transported_cuu_step_conditional": False,
        "single_cross_dust_projected_cuu_identity_derived": True,
        "projected_cuu_identity_derived": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "The standard dust EL projection is derived. The final hE=rho hCuu "
            "identity is closed for a single declared cross-dust pullback, but remains "
            "open for dynamic phi/L selection, mirror consistency, and pressure/Pi."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Projected Dust EL Cuu Derivation Chain",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Standard dust projection derived: {payload['standard_dust_projection_derived']}",
        f"Transported Cuu step conditional: {payload['transported_cuu_step_conditional']}",
        f"Single cross-dust projected Cuu identity derived: {payload['single_cross_dust_projected_cuu_identity_derived']}",
        f"Projected Cuu identity derived: {payload['projected_cuu_identity_derived']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Derivation Steps",
        "",
    ]
    for row in payload["derivation_steps"]:
        lines.append(f"- {row['step']}: `{row['formula']}`")
        lines.append(f"  - result: {row['result']}")
        lines.append(f"  - closed: {row['closed']}")
    lines.extend(["", "## Remaining Conditions", ""])
    lines.extend(f"- {item}" for item in payload["remaining_conditions"])
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
