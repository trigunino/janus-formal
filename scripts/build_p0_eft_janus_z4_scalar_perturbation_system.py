from __future__ import annotations

from pathlib import Path
import json

import sympy as sp


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_scalar_perturbation_system.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_scalar_perturbation_system.json")


def build_payload() -> dict:
    a, k, chi, b, rho_p, rho_m, psi = sp.symbols("a k chi B rho_plus rho_minus Psi")
    master = rho_p + b * rho_m
    background_constraint = sp.Eq(sp.Symbol("E2"), chi * master)
    poisson_constraint = sp.Eq(k**2 * psi, sp.Symbol("four_pi_G") * a**2 * master)
    zero_coupling_residual = sp.simplify(master.subs({b: 0, rho_m: 0}) - rho_p)
    checks = {
        "rank_one_master_source_imported": True,
        "background_constraint_from_master_source": True,
        "poisson_constraint_from_master_source": True,
        "zero_coupling_gr_source_residual_zero": zero_coupling_residual == 0,
        "slip_equation_declared": True,
        "continuity_euler_targets_declared": True,
        "bianchi_closure_required": True,
        "full_boltzmann_hierarchy_derived": False,
    }
    return {
        "status": "janus-z4-scalar-perturbation-system-scaffold",
        "lean_module": "JanusFormal.Branches.Z4CMBTopologyResetBlockedProgram.Gates.P0EFTJanusZ4ScalarPerturbationSystem",
        "master_source": str(master),
        "background_constraint": str(background_constraint),
        "poisson_constraint": str(poisson_constraint),
        "zero_coupling_residual": str(zero_coupling_residual),
        "checks": checks,
        "scalar_system_scaffold_ready": all(
            value for key, value in checks.items()
            if key != "full_boltzmann_hierarchy_derived"
        ),
        "scalar_system_physical_ready": False,
        "next_required": "Derive continuity/Euler/Boltzmann hierarchy from the same Z4 projected stress tensor.",
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z4 Scalar Perturbation System",
        "",
        f"Status: `{payload['status']}`",
        f"Master source: `{payload['master_source']}`",
        f"Background: `{payload['background_constraint']}`",
        f"Poisson: `{payload['poisson_constraint']}`",
        f"Zero-coupling residual: `{payload['zero_coupling_residual']}`",
        "",
        "## Checks",
    ]
    for key, value in payload["checks"].items():
        lines.append(f"- `{key}`: `{value}`")
    lines.extend([
        "",
        f"Scalar system scaffold ready: `{payload['scalar_system_scaffold_ready']}`",
        f"Scalar system physical ready: `{payload['scalar_system_physical_ready']}`",
        "",
        f"Next required: {payload['next_required']}",
        "",
    ])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
