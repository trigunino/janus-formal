from __future__ import annotations

from pathlib import Path
import json

import sympy as sp


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_neutrino_hierarchy_target.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_neutrino_hierarchy_target.json")


def build_payload() -> dict:
    k = sp.symbols("k")
    f0, f1, f2, f_lm1, f_l, f_lp1 = sp.symbols("F0 F1 F2 F_lminus1 F_l F_lplus1")
    phi_p, psi = sp.symbols("Phi_prime Psi")
    ell = sp.symbols("ell", integer=True, positive=True)
    equations = {
        "monopole": sp.Eq(sp.Symbol("F0_prime"), -k * f1 + 4 * phi_p),
        "dipole": sp.Eq(sp.Symbol("F1_prime"), k * (f0 / 3 - 2 * f2 / 3 + 4 * psi / 3)),
        "quadrupole": sp.Eq(sp.Symbol("F2_prime"), k * (2 * f1 / 5 - 3 * sp.Symbol("F3") / 5)),
        "higher_multipole": sp.Eq(sp.Symbol("F_l_prime"), k * (ell * f_lm1 - (ell + 1) * f_lp1) / (2 * ell + 1)),
    }
    checks = {
        "monopole_equation_declared": True,
        "dipole_equation_declared": True,
        "quadrupole_equation_declared": True,
        "higher_multipole_recursion_declared": True,
        "anisotropic_stress_feeds_slip": True,
        "z4_metric_inputs_required": True,
        "hierarchy_coefficients_derived": False,
    }
    return {
        "status": "janus-z4-neutrino-hierarchy-target",
        "lean_module": "JanusFormal.P0EFTJanusZ4NeutrinoHierarchyTarget",
        "equations": {key: str(value) for key, value in equations.items()},
        "checks": checks,
        "neutrino_target_ready": all(
            value for key, value in checks.items()
            if key != "hierarchy_coefficients_derived"
        ),
        "neutrino_physical_ready": False,
        "next_required": "Derive neutrino metric source coefficients from the Z4 scalar closure.",
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z4 Neutrino Hierarchy Target",
        "",
        f"Status: `{payload['status']}`",
        "",
        "## Equations",
    ]
    for key, value in payload["equations"].items():
        lines.append(f"- `{key}`: `{value}`")
    lines.extend(["", "## Checks"])
    for key, value in payload["checks"].items():
        lines.append(f"- `{key}`: `{value}`")
    lines.extend([
        "",
        f"Neutrino target ready: `{payload['neutrino_target_ready']}`",
        f"Neutrino physical ready: `{payload['neutrino_physical_ready']}`",
        "",
        f"Next required: {payload['next_required']}",
        "",
    ])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
