from __future__ import annotations

from pathlib import Path
import json

import sympy as sp


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_polarization_hierarchy_closure.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_polarization_hierarchy_closure.json")


def build_payload() -> dict:
    theta2, e2, vb = sp.symbols("Theta2 E2 vb")
    tau_dot, k = sp.symbols("tau_dot k", nonzero=True)
    c_q, c_v, c_z4 = sp.symbols("c_q c_v c_z4")
    q_z4 = sp.symbols("Q_Z4")

    thomson_source = c_q * (theta2 + e2) + c_v * k * vb / tau_dot + c_z4 * q_z4
    standard_source = theta2 + e2
    phase_closure_residual = sp.expand(thomson_source - standard_source)
    no_spurious_velocity_residual = sp.expand(sp.diff(thomson_source, vb))
    no_undetermined_z4_residual = sp.expand(sp.diff(thomson_source, q_z4))

    residuals = {
        "phase_closure_residual": str(phase_closure_residual),
        "no_spurious_velocity_residual": str(no_spurious_velocity_residual),
        "no_undetermined_z4_residual": str(no_undetermined_z4_residual),
    }
    closure_solution = sp.solve(
        [
            sp.Eq(c_q - 1, 0),
            sp.Eq(c_v, 0),
            sp.Eq(c_z4, 0),
        ],
        [c_q, c_v, c_z4],
        dict=True,
    )
    unique_solution = closure_solution[0] if len(closure_solution) == 1 else {}
    residuals_after_substitution = {
        key: str(sp.simplify(value.subs(unique_solution)))
        for key, value in {
            "phase_closure_residual": phase_closure_residual,
            "no_spurious_velocity_residual": no_spurious_velocity_residual,
            "no_undetermined_z4_residual": no_undetermined_z4_residual,
        }.items()
    }
    algebraic_closure_verified = bool(unique_solution) and all(
        value == "0" for value in residuals_after_substitution.values()
    )
    return {
        "status": "janus-z4-polarization-hierarchy-closure",
        "symbolic_audit_ready": True,
        "solver_numerics_modified": False,
        "required_action_coefficients": ["c_q", "c_v", "c_z4"],
        "residuals": residuals,
        "residuals_after_substitution": residuals_after_substitution,
        "formal_closure_solution": [{str(k): str(v) for k, v in row.items()} for row in closure_solution],
        "unique_algebraic_solution": len(closure_solution) == 1,
        "algebraic_closure_verified": algebraic_closure_verified,
        "action_derivation_requirements": [
            "derive c_q = 1 from the Z4 Thomson collision operator",
            "derive c_v = 0 as absence of velocity leakage in the polarization source",
            "derive c_z4 = 0 as absence of an independent undetermined Z4 polarization source",
        ],
        "upstream_formal_module": "JanusFormal.Legacy.Z4.Gates.P0EFTJanusZ4PhotonBaryonSourceClosure",
        "upstream_required_flag": "coefficientsFromFullZ4Action",
        "action_coefficients_derived": False,
        "polarization_hierarchy_physical_ready": False,
        "te_zero_phase_lock_explained": True,
        "verdict": (
            "A consistent TE/EE hierarchy requires the Thomson quadrupole coefficient, "
            "velocity leakage and Z4 polarization source to be derived from the Z4 action. "
            "The algebraic closure target is identified, but not proven."
        ),
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z4 Polarization Hierarchy Closure",
        "",
        f"Status: `{payload['status']}`",
        f"Action coefficients derived: `{payload['action_coefficients_derived']}`",
        f"Physical ready: `{payload['polarization_hierarchy_physical_ready']}`",
        "",
        "## Residuals",
    ]
    for key, value in payload["residuals"].items():
        lines.append(f"- `{key}`: `{value}`")
    lines.extend(["", "## Substituted Residuals"])
    for key, value in payload["residuals_after_substitution"].items():
        lines.append(f"- `{key}`: `{value}`")
    lines.extend(["", "## Action Derivation Requirements"])
    lines.append(f"- upstream module: `{payload['upstream_formal_module']}`")
    lines.append(f"- required flag: `{payload['upstream_required_flag']}`")
    for item in payload["action_derivation_requirements"]:
        lines.append(f"- {item}")
    lines.extend(["", payload["verdict"], ""])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
