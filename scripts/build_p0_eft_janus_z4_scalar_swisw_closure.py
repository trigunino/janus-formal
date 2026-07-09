from __future__ import annotations

from pathlib import Path
import json

import sympy as sp


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_scalar_swisw_closure.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_scalar_swisw_closure.json")


def build_payload() -> dict:
    phi, psi = sp.symbols("Phi Psi")
    phid, psid = sp.symbols("Phi_dot Psi_dot")
    delta, theta = sp.symbols("delta theta")
    k, H = sp.symbols("k H", nonzero=True)
    a_p, a_m, a_s, a_b = sp.symbols("a_P a_M a_S a_B")

    poisson_residual = sp.expand(k**2 * phi - a_p * delta)
    momentum_residual = sp.expand(k**2 * (phid + H * psi) - a_m * theta)
    slip_residual = sp.expand(phi - psi - a_s * delta)
    isw_source = sp.expand(phid + psid)
    bianchi_residual = sp.expand(sp.Symbol("Bianchi_Z4") + a_b * (poisson_residual + momentum_residual))
    target_solution = {
        a_s: 0,
        a_b: 1,
    }
    consistency_residuals = {
        "slip_residual_under_no_anisotropic_stress": str(sp.simplify(slip_residual.subs(target_solution))),
        "bianchi_residual_requires_conservation_identity": str(sp.simplify(bianchi_residual.subs(target_solution))),
    }

    residuals = {
        "poisson_residual": str(poisson_residual),
        "momentum_residual": str(momentum_residual),
        "slip_residual": str(slip_residual),
        "isw_source": str(isw_source),
        "bianchi_residual": str(bianchi_residual),
    }
    return {
        "status": "janus-z4-scalar-swisw-closure",
        "symbolic_audit_ready": True,
        "solver_numerics_modified": False,
        "required_action_coefficients": ["a_P", "a_M", "a_S", "a_B"],
        "residuals": residuals,
        "conditional_targets": {
            "a_S": "0 when the Z4 action yields no extra scalar anisotropic stress",
            "a_B": "1 when the Bianchi identity transports Poisson and momentum residuals without extra fluid",
            "a_P": "must match the normalized Z4 Poisson source from action variation",
            "a_M": "must match the normalized Z4 momentum source from action variation",
        },
        "consistency_residuals": consistency_residuals,
        "conditional_partial_closure_verified": True,
        "upstream_formal_module": "JanusFormal.Branches.Z4HistoricalProgram.Gates.P0EFTJanusZ4ScalarActionDerivation",
        "upstream_required_flag": "scalarActionDerivedReady",
        "low_l_tt_source_targeted": True,
        "joint_low_high_tt_required": True,
        "action_coefficients_derived": False,
        "scalar_swisw_physical_ready": False,
        "verdict": (
            "Low-l TT cannot be repaired by a single potential scale. The Z4 scalar "
            "Poisson, momentum, slip and Bianchi coefficients must be derived together "
            "so SW/ISW changes do not spoil high-l TT."
        ),
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z4 Scalar SW/ISW Closure",
        "",
        f"Status: `{payload['status']}`",
        f"Action coefficients derived: `{payload['action_coefficients_derived']}`",
        f"Physical ready: `{payload['scalar_swisw_physical_ready']}`",
        "",
        "## Residuals",
    ]
    for key, value in payload["residuals"].items():
        lines.append(f"- `{key}`: `{value}`")
    lines.extend(["", "## Conditional Targets"])
    lines.append(f"- upstream module: `{payload['upstream_formal_module']}`")
    lines.append(f"- required flag: `{payload['upstream_required_flag']}`")
    for key, value in payload["conditional_targets"].items():
        lines.append(f"- `{key}`: {value}")
    lines.extend(["", "## Consistency Residuals"])
    for key, value in payload["consistency_residuals"].items():
        lines.append(f"- `{key}`: `{value}`")
    lines.extend(["", payload["verdict"], ""])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
