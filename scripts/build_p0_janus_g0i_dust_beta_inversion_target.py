from __future__ import annotations

from pathlib import Path
import json

import sympy as sp


REPORT_PATH = Path("outputs/reports/p0_janus_g0i_dust_beta_inversion_target.md")
JSON_PATH = Path("outputs/reports/p0_janus_g0i_dust_beta_inversion_target.json")


def beta_minus_to_plus_from_plus_g0i() -> sp.Expr:
    lap_b, chi, rho_plus, beta_plus, b4, rho_minus_to_plus = sp.symbols(
        "LapB_plus_i chi rho_plus beta_plus_i B_4vol_plus_from_minus rho_minus_to_plus"
    )
    return sp.simplify((-lap_b / (2 * chi) - rho_plus * beta_plus) / (b4 * rho_minus_to_plus))


def beta_plus_to_minus_from_minus_g0i() -> sp.Expr:
    lap_b, chi, rho_minus, beta_minus, b4, rho_plus_to_minus = sp.symbols(
        "LapB_minus_i chi rho_minus beta_minus_i B_4vol_minus_from_plus rho_plus_to_minus"
    )
    return sp.simplify((lap_b / (2 * chi) - rho_minus * beta_minus) / (b4 * rho_plus_to_minus))


def build_payload() -> dict:
    return {
        "description": "Conditional dust inversion of Janus transverse G0i rows into cross-sector beta_i.",
        "status": "g0i-dust-beta-inversion-target-open",
        "depends_on": [
            "p0_janus_weakfield_g0i_shift_operator_derivation",
            "p0_janus_pressure_pi0i_transport_derivation",
        ],
        "assumptions": [
            "linear weak-field transverse/quasistatic shift row",
            "dust branch p=0 and Pi0i=0",
            "nonzero transported density and B_4vol denominator",
            "same-L boost convention already declared",
        ],
        "plus_receiver_beta_minus_to_plus": sp.sstr(beta_minus_to_plus_from_plus_g0i()),
        "minus_receiver_beta_plus_to_minus": sp.sstr(beta_plus_to_minus_from_minus_g0i()),
        "denominator_conditions": [
            "B_4vol_plus_from_minus rho_minus_to_plus != 0",
            "B_4vol_minus_from_plus rho_plus_to_minus != 0",
        ],
        "not_allowed": [
            "use this inversion when p or Pi0i is nonzero",
            "fit beta_i to lensing residuals",
            "absorb missing pressure/Pi0i into Q_cross",
        ],
        "g0i_dust_inversion_written": True,
        "conditional_dust_beta_available": True,
        "perfect_fluid_beta_available": False,
        "anisotropic_beta_available": False,
        "source_derived_beta_available_for_general_matter": False,
        "uses_observational_fit": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "In the dust transverse branch, G0i gives an explicit beta inversion. "
            "It is not valid for pressure or anisotropic-stress matter until those source terms close."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Janus G0i Dust Beta Inversion Target",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Beta minus_to_plus: `{payload['plus_receiver_beta_minus_to_plus']}`",
        f"Beta plus_to_minus: `{payload['minus_receiver_beta_plus_to_minus']}`",
        f"Conditional dust beta available: {payload['conditional_dust_beta_available']}",
        f"Perfect-fluid beta available: {payload['perfect_fluid_beta_available']}",
        f"Anisotropic beta available: {payload['anisotropic_beta_available']}",
        f"Uses observational fit: {payload['uses_observational_fit']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Assumptions",
        "",
    ]
    lines.extend(f"- {item}" for item in payload["assumptions"])
    lines.extend(["", "## Denominator Conditions", ""])
    lines.extend(f"- `{item}`" for item in payload["denominator_conditions"])
    lines.extend(["", "## Not Allowed", ""])
    lines.extend(f"- {item}" for item in payload["not_allowed"])
    lines.extend(["", f"Verdict: {payload['verdict']}", ""])
    return "\n".join(lines)


def write_reports(report_path: Path = REPORT_PATH, json_path: Path = JSON_PATH) -> dict:
    report_path.parent.mkdir(parents=True, exist_ok=True)
    json_path.parent.mkdir(parents=True, exist_ok=True)
    payload = build_payload()
    json_path.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    report_path.write_text(render_markdown(payload), encoding="utf-8")
    return payload


def main() -> None:
    write_reports()
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {JSON_PATH}")


if __name__ == "__main__":
    main()
