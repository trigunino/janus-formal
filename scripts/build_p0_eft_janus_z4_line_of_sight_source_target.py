from __future__ import annotations

from pathlib import Path
import json

import sympy as sp


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_line_of_sight_source_target.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_line_of_sight_source_target.json")


def build_payload() -> dict:
    g, theta0, psi, phi, vb, pi_pol = sp.symbols("g Theta0 Psi Phi v_b Pi_pol")
    psi_p, phi_p = sp.symbols("Psi_prime Phi_prime")
    sw = sp.simplify(g * (theta0 + psi))
    doppler = sp.simplify(g * vb)
    isw = sp.simplify(sp.exp(-sp.Symbol("tau")) * (psi_p + phi_p))
    pol = sp.simplify(g * pi_pol)
    total = sp.simplify(sw + doppler + isw + pol)
    checks = {
        "visibility_source_declared": True,
        "sw_source_declared": True,
        "doppler_source_declared": True,
        "isw_source_declared": True,
        "polarization_source_declared": True,
        "z4_metric_inputs_required": True,
        "source_coefficients_derived": False,
    }
    return {
        "status": "janus-z4-line-of-sight-source-target",
        "lean_module": "JanusFormal.Branches.Z4HistoricalProgram.Gates.P0EFTJanusZ4LineOfSightSourceTarget",
        "sw_source": str(sw),
        "doppler_source": str(doppler),
        "isw_source": str(isw),
        "polarization_source": str(pol),
        "total_source": str(total),
        "checks": checks,
        "los_target_ready": all(value for key, value in checks.items() if key != "source_coefficients_derived"),
        "los_physical_ready": False,
        "next_required": "Derive Theta0, Psi, Phi, v_b and Pi_pol from the Z4 hierarchy solution.",
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z4 Line-Of-Sight Source Target",
        "",
        f"Status: `{payload['status']}`",
        f"SW: `{payload['sw_source']}`",
        f"Doppler: `{payload['doppler_source']}`",
        f"ISW: `{payload['isw_source']}`",
        f"Polarization: `{payload['polarization_source']}`",
        f"Total: `{payload['total_source']}`",
        "",
        "## Checks",
    ]
    for key, value in payload["checks"].items():
        lines.append(f"- `{key}`: `{value}`")
    lines.extend(["", f"LOS target ready: `{payload['los_target_ready']}`", f"LOS physical ready: `{payload['los_physical_ready']}`", "", f"Next required: {payload['next_required']}", ""])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
