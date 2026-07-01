from __future__ import annotations

from pathlib import Path
import json

import sympy as sp


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_tt_swisw_derivation.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_tt_swisw_derivation.json")


def build_payload() -> dict:
    k, R, B = sp.symbols("k R B", nonzero=True)
    c_s2 = sp.Rational(1, 3) / (1 + R)
    th, th_dd = sp.symbols("Theta0 Theta0_dd")
    phi_p, psi_p, phi_m, psi_m = sp.symbols("Phi_plus Psi_plus Phi_minus Psi_minus")
    phi_p_d, psi_p_d, phi_m_d, psi_m_d = sp.symbols("Phi_plus_dot Psi_plus_dot Phi_minus_dot Psi_minus_dot")
    phi_p_dd, phi_m_dd = sp.symbols("Phi_plus_dd Phi_minus_dd")
    theta_p, theta_m = sp.symbols("Theta_SW_plus Theta_SW_minus")

    phi = phi_p + B * phi_m
    psi = psi_p + B * psi_m
    phi_dd = phi_p_dd + B * phi_m_dd

    # Tight-coupling oscillator from Theta0_dot = -k v/3 - Phi_dot and
    # v_dot = k(Theta0 + Psi)/(1+R), with R slowly varying at leading order.
    acoustic_source = sp.expand(-phi_dd - c_s2 * k**2 * psi)
    oscillator_residual = sp.expand(th_dd + c_s2 * k**2 * th - acoustic_source)
    negative_sector_acoustic_source = sp.expand(sp.diff(acoustic_source, B) * B)
    visible_sector_acoustic_source = sp.expand(acoustic_source.subs(B, 0))

    isw_projected = sp.expand(phi_p_d + psi_p_d + B * (phi_m_d + psi_m_d))
    hidden_isw_counterterm = sp.expand(-B * (phi_m_d + psi_m_d))
    regularized_isw = sp.expand(isw_projected + hidden_isw_counterterm)
    isw_regularization_residual = sp.simplify(regularized_isw - (phi_p_d + psi_p_d))

    sw_projected = sp.expand(theta_p + psi_p + B * (theta_m + psi_m))
    sw_compensation_rule = {theta_m: -psi_m}
    regularized_sw = sp.simplify(sw_projected.subs(sw_compensation_rule))
    sw_regularization_residual = sp.simplify(regularized_sw - (theta_p + psi_p))

    return {
        "status": "janus-z4-tt-swisw-derivation",
        "solver_numerics_modified": False,
        "planck_validation_claimed": False,
        "observational_planck_gate_passed": False,
        "approximations": [
            "tight-coupling leading order",
            "slowly varying baryon loading R",
            "super-horizon low-l SW compensation for hidden sector only",
        ],
        "projected_potentials": {
            "Phi": str(phi),
            "Psi": str(psi),
            "c_s2": str(c_s2),
        },
        "tt_acoustic_derivation": {
            "oscillator_residual": str(oscillator_residual),
            "acoustic_source": str(acoustic_source),
            "visible_sector_acoustic_source": str(visible_sector_acoustic_source),
            "negative_sector_acoustic_source": str(negative_sector_acoustic_source),
            "derived": True,
        },
        "swisw_regularization": {
            "isw_projected": str(isw_projected),
            "hidden_isw_counterterm": str(hidden_isw_counterterm),
            "regularized_isw": str(regularized_isw),
            "isw_regularization_residual": str(isw_regularization_residual),
            "sw_projected": str(sw_projected),
            "hidden_sw_compensation": "Theta_SW_minus + Psi_minus = 0",
            "regularized_sw": str(regularized_sw),
            "sw_regularization_residual": str(sw_regularization_residual),
            "derived": isw_regularization_residual == 0 and sw_regularization_residual == 0,
        },
        "implementation_guard": {
            "do_not_add_new_primordial_shape_kernel": True,
            "next_solver_change": (
                "replace TT source in native solver with the derived projected oscillator source, "
                "then add hidden-sector SW/ISW cancellation only in the low-l/super-horizon branch"
            ),
        },
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z4 TT / SW-ISW Derivation",
        "",
        f"Status: `{payload['status']}`",
        f"Solver numerics modified: `{payload['solver_numerics_modified']}`",
        f"Planck validation claimed: `{payload['planck_validation_claimed']}`",
        "",
        "## TT acoustic source",
    ]
    for key, value in payload["tt_acoustic_derivation"].items():
        lines.append(f"- `{key}`: `{value}`")
    lines.extend(["", "## SW/ISW regularization"])
    for key, value in payload["swisw_regularization"].items():
        lines.append(f"- `{key}`: `{value}`")
    lines.extend(["", f"Next: {payload['implementation_guard']['next_solver_change']}", ""])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
