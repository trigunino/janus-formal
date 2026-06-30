from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_stueckelberg_zero_param_dust_compatibility.md")
JSON_PATH = Path("outputs/reports/p0_stueckelberg_zero_param_dust_compatibility.json")


def build_payload() -> dict:
    branch = {
        "name": "zero_parameter_normalized_copy",
        "free_parameters": [],
        "fit_to_observations": False,
        "normalization_rule": "Phi and Phi_bar coefficients are fixed by exact M15/M30 determinant source normalization",
        "prediction_ready": False,
    }
    compatibility_conditions = [
        {
            "id": "C1",
            "name": "transported_plus_dust_continuity",
            "equation": "nabla_plus_mu(rho_plus u_plus^mu)=0",
            "role": "plus dust must be conserved before pullback/pushforward",
        },
        {
            "id": "C2",
            "name": "transported_minus_dust_continuity",
            "equation": "nabla_minus_a(rho_minus u_minus^a)=0",
            "role": "minus dust must be conserved before pullback/pushforward",
        },
        {
            "id": "C3",
            "name": "phi_pullback_density_map",
            "equation": "rho_minus_to_plus(x)=J_phi(x) rho_minus(phi(x))",
            "role": "Phi uses the density copied from minus to plus by the Stueckelberg map",
        },
        {
            "id": "C4",
            "name": "phi_pushforward_density_map",
            "equation": "rho_plus_to_minus(y)=J_phi_inv(y) rho_plus(phi^{-1}(y))",
            "role": "Phi_bar uses the mirror density copied from plus to minus",
        },
        {
            "id": "C5",
            "name": "E_phi",
            "equation": "delta S / delta phi = 0",
            "role": "map stationarity must be compatible with C1-C4, not imposed by fit",
        },
        {
            "id": "C6",
            "name": "E_L",
            "equation": "delta S / delta L = 0",
            "role": "Lorentz-frame stationarity must be compatible with C1-C4 and E_phi",
        },
        {
            "id": "C7",
            "name": "same_L_for_K_and_Qcross",
            "equation": "K_plus, K_minus, and Q_cross are all induced by the same phi/L",
            "role": "no independent L or map may be introduced for cross terms",
        },
    ]
    closure_decision = {
        "compatibility_closes": False,
        "conditional_closure_possible": True,
        "reason": (
            "The zero-parameter normalization fixes amplitudes and forbids fit parameters, "
            "but E_phi/E_L still add map PDE constraints that need not follow from transported "
            "dust continuity and the density maps."
        ),
        "required_for_closure": [
            "derive E_phi from C1-C4 plus normalization",
            "derive E_L from the same phi/L data used by K_plus, K_minus, and Q_cross",
            "show no hidden boundary, gauge, or density-convention fit enters",
        ],
    }
    return {
        "description": "Bounded P0 artifact for zero-parameter Stueckelberg dust E_phi/E_L compatibility.",
        "status": "zero-param-dust-compatibility-conditional-open",
        "source_derived": False,
        "new_axiom": True,
        "physics_closed": False,
        "prediction_ready": False,
        "branch": branch,
        "compatibility_conditions": compatibility_conditions,
        "closure_decision": closure_decision,
        "verdict": (
            "The no-fit zero_parameter_normalized_copy branch is explicit enough to test, "
            "but compatibility does not close unconditionally. It remains conditional on "
            "deriving E_phi and E_L from the transported dust density maps using the same L."
        ),
    }


def render_markdown(payload: dict) -> str:
    branch = payload["branch"]
    decision = payload["closure_decision"]
    lines = [
        "# P0 Stueckelberg Zero-Parameter Dust Compatibility",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Source derived: {payload['source_derived']}",
        f"New axiom: {payload['new_axiom']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Branch",
        "",
        f"Name: {branch['name']}",
        f"Free parameters: {branch['free_parameters']}",
        f"Fit to observations: {branch['fit_to_observations']}",
        f"Normalization: {branch['normalization_rule']}",
        "",
        "## Compatibility Conditions",
        "",
    ]
    for row in payload["compatibility_conditions"]:
        lines.append(f"- {row['id']} {row['name']}: `{row['equation']}`; {row['role']}")
    lines.extend(
        [
            "",
            "## Closure Decision",
            "",
            f"Compatibility closes: {decision['compatibility_closes']}",
            f"Conditional closure possible: {decision['conditional_closure_possible']}",
            f"Reason: {decision['reason']}",
            "",
            "## Required For Closure",
            "",
        ]
    )
    lines.extend(f"- {item}" for item in decision["required_for_closure"])
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
