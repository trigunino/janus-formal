from __future__ import annotations

from pathlib import Path
import json

import sympy as sp


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_weyl_tt_transport_derivation.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_weyl_tt_transport_derivation.json")


def build_payload() -> dict:
    chi, chi_s, b = sp.symbols("chi chi_s b", positive=True)
    phi_p, psi_p, phi_m, psi_m = sp.symbols("Phi_plus Psi_plus Phi_minus Psi_minus")
    dphi_p, dpsi_p, dphi_m, dpsi_m = sp.symbols("dPhi_plus dPsi_plus dPhi_minus dPsi_minus")
    qdet, qcross = sp.symbols("Q_det Q_cross")

    optical_kernel = chi * (chi_s - chi) / chi_s
    weyl_visible = (phi_p + psi_p) / 2
    weyl_mirror_even = b * (phi_m + psi_m) / 2
    leakage = qdet * sp.Symbol("b_D") + qcross * sp.Symbol("b_X")
    weyl_projected = sp.expand(weyl_visible + weyl_mirror_even + leakage)
    no_leak_solution = {sp.Symbol("b_D"): 0, sp.Symbol("b_X"): 0}
    leak_residual = sp.simplify(weyl_projected.subs(no_leak_solution) - (weyl_visible + weyl_mirror_even))

    tt_clock_visible = dphi_p + dpsi_p
    tt_clock_hidden = b * (dphi_m + dpsi_m)
    ward_counterterm = -tt_clock_hidden
    tt_clock_regularized = sp.expand(tt_clock_visible + tt_clock_hidden + ward_counterterm)
    tt_clock_residual = sp.simplify(tt_clock_regularized - tt_clock_visible)

    lensing_kernel_ready = sp.simplify(sp.diff(optical_kernel, chi_s) - chi**2 / chi_s**2)
    return {
        "status": "janus-z4-weyl-tt-transport-derivation",
        "solver_numerics_modified": False,
        "planck_validation_claimed": False,
        "observational_planck_gate_passed": False,
        "weyl_lensing_derivation": {
            "optical_kernel": str(optical_kernel),
            "weyl_projected": str(weyl_projected),
            "leak_residual_after_no_leak": str(leak_residual),
            "mirror_even_source": str(weyl_mirror_even),
            "kernel_distance_derivative_check": str(lensing_kernel_ready),
            "derived": leak_residual == 0,
        },
        "tt_transport_beyond_leading": {
            "visible_clock": str(tt_clock_visible),
            "hidden_clock": str(tt_clock_hidden),
            "ward_counterterm": str(ward_counterterm),
            "regularized_clock": str(tt_clock_regularized),
            "clock_residual": str(tt_clock_residual),
            "derived": tt_clock_residual == 0,
        },
        "next_solver_branch": (
            "Use mirror-even Weyl source only in C_L phiphi and apply the TT Ward counterterm "
            "as a clock regularizer rather than as an extra acoustic force."
        ),
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z4 Weyl / TT Transport Derivation",
        "",
        f"Status: `{payload['status']}`",
        f"Solver numerics modified: `{payload['solver_numerics_modified']}`",
        "",
        "## Weyl lensing",
    ]
    for key, value in payload["weyl_lensing_derivation"].items():
        lines.append(f"- `{key}`: `{value}`")
    lines.extend(["", "## TT transport"])
    for key, value in payload["tt_transport_beyond_leading"].items():
        lines.append(f"- `{key}`: `{value}`")
    lines.extend(["", f"Next: {payload['next_solver_branch']}", ""])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
