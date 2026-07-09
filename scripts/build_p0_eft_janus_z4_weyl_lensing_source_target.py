from __future__ import annotations

from pathlib import Path
import json

import sympy as sp


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_weyl_lensing_source_target.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_weyl_lensing_source_target.json")


def build_payload() -> dict:
    phi, psi, chi, chi_s, k = sp.symbols("Phi Psi chi chi_s k", positive=True)
    weyl = sp.simplify((phi + psi) / 2)
    kernel = sp.simplify((chi_s - chi) * chi / chi_s)
    finite_transfer_target = sp.simplify(k**2 * weyl)
    checks = {
        "weyl_potential_declared": True,
        "lensing_kernel_declared": True,
        "z4_slip_inputs_required": True,
        "determinant_projection_required": True,
        "finite_transfer_target_declared": True,
        "source_coefficients_derived": False,
    }
    return {
        "status": "janus-z4-weyl-lensing-source-target",
        "lean_module": "JanusFormal.Branches.Z4HistoricalProgram.Gates.P0EFTJanusZ4WeylLensingSourceTarget",
        "weyl_potential": str(weyl),
        "lensing_kernel": str(kernel),
        "finite_transfer_target": str(finite_transfer_target),
        "checks": checks,
        "weyl_lensing_target_ready": all(value for key, value in checks.items() if key != "source_coefficients_derived"),
        "weyl_lensing_physical_ready": False,
        "next_required": "Derive Phi+Psi and determinant projection from the Z4 scalar closure.",
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z4 Weyl Lensing Source Target",
        "",
        f"Status: `{payload['status']}`",
        f"Weyl: `{payload['weyl_potential']}`",
        f"Kernel: `{payload['lensing_kernel']}`",
        f"Transfer target: `{payload['finite_transfer_target']}`",
        "",
        "## Checks",
    ]
    for key, value in payload["checks"].items():
        lines.append(f"- `{key}`: `{value}`")
    lines.extend(["", f"Weyl lensing target ready: `{payload['weyl_lensing_target_ready']}`", f"Weyl lensing physical ready: `{payload['weyl_lensing_physical_ready']}`", "", f"Next required: {payload['next_required']}", ""])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
