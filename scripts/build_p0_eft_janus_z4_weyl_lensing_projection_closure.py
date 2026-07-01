from __future__ import annotations

from pathlib import Path
import json

import sympy as sp


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_weyl_lensing_projection_closure.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_weyl_lensing_projection_closure.json")


def build_payload() -> dict:
    chi, chi_star = sp.symbols("chi chi_star", positive=True)
    phi, psi, qdet, qcross = sp.symbols("Phi Psi Q_det Q_cross")
    b_w, b_d, b_x, b_g = sp.symbols("b_W b_D b_X b_G")

    gr_kernel = (chi_star - chi) / (chi_star * chi)
    z4_kernel = b_g * gr_kernel
    weyl_source = b_w * (phi + psi) / 2 + b_d * qdet + b_x * qcross
    kernel_residual = sp.expand(z4_kernel - gr_kernel)
    source_residual = sp.expand(weyl_source - (phi + psi) / 2)
    no_det_leakage_residual = sp.diff(weyl_source, qdet)
    no_cross_leakage_residual = sp.diff(weyl_source, qcross)

    residuals = {
        "kernel_residual": str(kernel_residual),
        "source_residual": str(source_residual),
        "no_det_leakage_residual": str(no_det_leakage_residual),
        "no_cross_leakage_residual": str(no_cross_leakage_residual),
    }
    closure_solution = sp.solve(
        [
            sp.Eq(b_g - 1, 0),
            sp.Eq(b_w - 1, 0),
            sp.Eq(b_d, 0),
            sp.Eq(b_x, 0),
        ],
        [b_g, b_w, b_d, b_x],
        dict=True,
    )
    unique_solution = closure_solution[0] if len(closure_solution) == 1 else {}
    residuals_after_substitution = {
        key: str(sp.simplify(value.subs(unique_solution)))
        for key, value in {
            "kernel_residual": kernel_residual,
            "source_residual": source_residual,
            "no_det_leakage_residual": no_det_leakage_residual,
            "no_cross_leakage_residual": no_cross_leakage_residual,
        }.items()
    }
    algebraic_projection_verified = bool(unique_solution) and all(
        value == "0" for value in residuals_after_substitution.values()
    )
    return {
        "status": "janus-z4-weyl-lensing-projection-closure",
        "symbolic_audit_ready": True,
        "solver_numerics_modified": False,
        "required_geometric_coefficients": ["b_G", "b_W", "b_D", "b_X"],
        "residuals": residuals,
        "residuals_after_substitution": residuals_after_substitution,
        "formal_closure_solution": [{str(k): str(v) for k, v in row.items()} for row in closure_solution],
        "unique_algebraic_solution": len(closure_solution) == 1,
        "algebraic_projection_verified": algebraic_projection_verified,
        "geodesic_derivation_requirements": [
            "derive b_G = 1 from the Z4 photon geodesic projection",
            "derive b_W = 1 from the positive-sector Weyl observable map",
            "derive b_D = 0 as absence of determinant leakage into lensing",
            "derive b_X = 0 as absence of independent cross-sector leakage into lensing",
        ],
        "upstream_formal_module": "JanusFormal.P0EFTJanusZ4WeylLensingSourceTarget",
        "upstream_required_flag": "sourceCoefficientsDerived",
        "geodesic_projection_derived": False,
        "weyl_source_derived": False,
        "lensing_projection_physical_ready": False,
        "verdict": (
            "The lensing blocker is separated into geodesic kernel normalization and "
            "Z4 Weyl-source leakage. Amplitude-only scans cannot close these residuals."
        ),
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z4 Weyl Lensing Projection Closure",
        "",
        f"Status: `{payload['status']}`",
        f"Geodesic projection derived: `{payload['geodesic_projection_derived']}`",
        f"Weyl source derived: `{payload['weyl_source_derived']}`",
        f"Physical ready: `{payload['lensing_projection_physical_ready']}`",
        "",
        "## Residuals",
    ]
    for key, value in payload["residuals"].items():
        lines.append(f"- `{key}`: `{value}`")
    lines.extend(["", "## Substituted Residuals"])
    for key, value in payload["residuals_after_substitution"].items():
        lines.append(f"- `{key}`: `{value}`")
    lines.extend(["", "## Geodesic Derivation Requirements"])
    lines.append(f"- upstream module: `{payload['upstream_formal_module']}`")
    lines.append(f"- required flag: `{payload['upstream_required_flag']}`")
    for item in payload["geodesic_derivation_requirements"]:
        lines.append(f"- {item}")
    lines.extend(["", payload["verdict"], ""])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
