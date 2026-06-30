from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_stueckelberg_dphi_density_cancellation.md")
JSON_PATH = Path("outputs/reports/p0_stueckelberg_dphi_density_cancellation.json")


def build_payload() -> dict:
    density_maps = [
        {
            "direction": "minus_to_plus",
            "map": "rho_minus_to_plus(x)=J_phi(x) rho_minus(phi(x))",
            "continuity": "nabla_minus_a(rho_minus u_minus^a)=0 transported by phi",
            "dphi_terms_cancel": "conditional",
        },
        {
            "direction": "plus_to_minus",
            "map": "rho_plus_to_minus(y)=J_phi_inv(y) rho_plus(phi^{-1}(y))",
            "continuity": "nabla_plus_mu(rho_plus u_plus^mu)=0 transported by phi^{-1}",
            "dphi_terms_cancel": "conditional",
        },
    ]
    required_identities = [
        {
            "id": "I1",
            "name": "jacobian_volume_identity",
            "equation": "sqrt|g_plus|(x) J_phi(x)=phi^* sqrt|g_minus|(x)",
            "role": "turns the copied density into a true transported density, not a fitted scalar",
            "proven_here": False,
        },
        {
            "id": "I2",
            "name": "lie_derivative_density_relation",
            "equation": "L_u(J_phi phi^*rho)=J_phi phi^*(L_phi_*u rho)+rho_trans L_u log J_phi",
            "role": "pairs D_phi density terms with the transported dust continuity equation",
            "proven_here": False,
        },
        {
            "id": "I3",
            "name": "determinant_B_consistency",
            "equation": "D log B = D log J_phi + transported metric-volume terms",
            "role": "prevents an uncancelled determinant-measure gradient from being renamed away",
            "proven_here": False,
        },
    ]
    cancellation_tests = [
        {
            "target": "D_phi rho_minus_to_plus",
            "input": "phi pullback density map plus transported minus dust continuity",
            "cancels": "conditional_on_I1_I2_I3",
            "fit_used": False,
        },
        {
            "target": "D_phi rho_plus_to_minus",
            "input": "phi pushforward density map plus transported plus dust continuity",
            "cancels": "conditional_on_I1_I2_I3",
            "fit_used": False,
        },
    ]
    closure_decision = {
        "dphi_density_terms_cancel": "conditional",
        "closure": False,
        "conditional_closure_possible": True,
        "reason": (
            "The density maps and transported dust continuity give the right cancellation "
            "shape, but closure requires the Jacobian/volume identity, the Lie derivative "
            "density relation, and determinant B consistency to be derived with the same phi."
        ),
    }
    return {
        "description": (
            "Bounded P0 artifact testing whether phi pullback/pushforward density maps plus "
            "transported dust continuity cancel D_phi transported-density terms in the "
            "zero-parameter Stueckelberg dust branch."
        ),
        "status": "dphi-density-cancellation-conditional-open",
        "branch": "zero_parameter_normalized_copy",
        "fit_used": False,
        "free_parameters": [],
        "source_derived": False,
        "new_axiom": False,
        "physics_closed": False,
        "prediction_ready": False,
        "density_maps": density_maps,
        "required_identities": required_identities,
        "cancellation_tests": cancellation_tests,
        "closure_decision": closure_decision,
        "verdict": (
            "No-fit cancellation is plausible only conditionally. The D_phi transported-density "
            "terms are not marked closed until the required Jacobian/volume, Lie derivative, "
            "and determinant B identities are proven in the same Stueckelberg map convention."
        ),
    }


def render_markdown(payload: dict) -> str:
    decision = payload["closure_decision"]
    lines = [
        "# P0 Stueckelberg D_phi Density Cancellation",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Branch: {payload['branch']}",
        f"Fit used: {payload['fit_used']}",
        f"Free parameters: {payload['free_parameters']}",
        f"Source derived: {payload['source_derived']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Density Maps",
        "",
    ]
    for row in payload["density_maps"]:
        lines.append(f"- {row['direction']}: `{row['map']}`")
        lines.append(f"  - continuity: `{row['continuity']}`")
        lines.append(f"  - D_phi terms cancel: {row['dphi_terms_cancel']}")
    lines.extend(["", "## Required Identities", ""])
    for row in payload["required_identities"]:
        lines.append(f"- {row['id']} {row['name']}: `{row['equation']}`")
        lines.append(f"  - role: {row['role']}")
        lines.append(f"  - proven here: {row['proven_here']}")
    lines.extend(["", "## Cancellation Tests", ""])
    for row in payload["cancellation_tests"]:
        lines.append(f"- {row['target']}: {row['cancels']}")
        lines.append(f"  - input: {row['input']}")
        lines.append(f"  - fit used: {row['fit_used']}")
    lines.extend(
        [
            "",
            "## Closure Decision",
            "",
            f"D_phi density terms cancel: {decision['dphi_density_terms_cancel']}",
            f"Closure: {decision['closure']}",
            f"Conditional closure possible: {decision['conditional_closure_possible']}",
            f"Reason: {decision['reason']}",
            "",
            f"Verdict: {payload['verdict']}",
            "",
        ]
    )
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
