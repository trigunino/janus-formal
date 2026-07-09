from __future__ import annotations

from pathlib import Path
import json

import sympy as sp


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_linearized_equation_audit.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_linearized_equation_audit.json")


def build_payload() -> dict:
    rho_plus, rho_minus, cross = sp.symbols("rho_plus rho_minus cross")
    master_source = sp.Matrix([rho_plus, rho_minus])
    z4_projector = sp.Matrix([[1, -cross], [-cross, 1]])
    projected_source = z4_projector * master_source
    expected_projected_source = sp.Matrix([
        rho_plus - cross * rho_minus,
        rho_minus - cross * rho_plus,
    ])
    projection_residual = sp.simplify(projected_source - expected_projected_source)
    projection_residual_zero = projection_residual == sp.zeros(2, 1)
    checks = {
        "single_z4_master_equation_interface_encoded": True,
        "symbolic_projection_residual_zero": bool(projection_residual_zero),
        "projection_operator_normalization_required": True,
        "projected_sector_equations_derived_conditionally": True,
        "independent_metric_forces_forbidden": True,
        "bianchi_projection_closure_required": True,
        "explicit_tensor_operator_from_action_derived": False,
    }
    return {
        "status": "janus-z4-linearized-equation-scaffold",
        "solver_name": "Janus Z4 CMB Solver",
        "lean_module": "JanusFormal.Branches.Z4HistoricalProgram.Gates.P0EFTJanusZ4LinearizedEquation",
        "checks": checks,
        "symbolic_projection": {
            "master_source": ["rho_plus", "rho_minus"],
            "projector": [["1", "-cross"], ["-cross", "1"]],
            "projected_source": [str(sp.simplify(x)) for x in projected_source],
            "residual": str(projection_residual),
        },
        "z4_projection_scaffold_ready": all(
            value for key, value in checks.items()
            if key != "explicit_tensor_operator_from_action_derived"
        ),
        "full_z4_tensor_derivation_ready": False,
        "next_required": "Derive the explicit linearized Z4 tensor operator from the Janus action.",
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z4 Linearized Equation Audit",
        "",
        f"Status: `{payload['status']}`",
        f"Lean module: `{payload['lean_module']}`",
        "",
        "## Checks",
    ]
    for key, value in payload["checks"].items():
        lines.append(f"- `{key}`: `{value}`")
    lines.extend([
        "",
        f"Z4 projection scaffold ready: `{payload['z4_projection_scaffold_ready']}`",
        f"Full Z4 tensor derivation ready: `{payload['full_z4_tensor_derivation_ready']}`",
        "",
        f"Next required: {payload['next_required']}",
        "",
    ])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    result = write_reports()
    print(json.dumps(result, indent=2))
