from __future__ import annotations

from pathlib import Path
import json

import sympy as sp


REPORT_PATH = Path("outputs/reports/p0_dust_monoflux_cuu_conditional_closure.md")
JSON_PATH = Path("outputs/reports/p0_dust_monoflux_cuu_conditional_closure.json")


def build_payload() -> dict:
    rho, u0, u1, c0, c1, e0, e1 = sp.symbols("rho u0 u1 C0 C1 E0 E1")
    h00, h01, h10, h11 = sp.symbols("h00 h01 h10 h11")
    projected_el = sp.Matrix([h00 * e0 + h01 * e1, h10 * e0 + h11 * e1])
    projected_cuu = sp.Matrix(
        [
            rho * (h00 * c0 + h01 * c1) * (u0**2 + u1**2),
            rho * (h10 * c0 + h11 * c1) * (u0**2 + u1**2),
        ]
    )
    substitution = {e0: rho * c0 * (u0**2 + u1**2), e1: rho * c1 * (u0**2 + u1**2)}
    residual = sp.simplify(projected_el.subs(substitution) - projected_cuu)
    closure_conditions = [
        "cold monoflux dust branch: p=0 and Pi=0",
        "pulled dust action yields E_alpha=rho C_alpha(u,u)",
        "same projector h is used on both E_alpha and C_alpha(u,u)",
        "same phi/L/B4vol already selected for density and velocity pullback",
    ]
    still_open = [
        "derive E_alpha=rho C_alpha(u,u) from Janus action rather than substitute it",
        "derive same phi/L selection dynamically",
        "close D L and D log B4vol residual substitution",
        "prove mirror plus/minus residuals R_plus=R_minus=0",
        "exclude multistreaming or switch to full Vlasov",
    ]
    return {
        "description": "Conditional algebraic closure of projected Cuu on the cold monoflux dust branch.",
        "status": "dust-monoflux-cuu-conditional-closure",
        "projected_residual": [str(item) for item in residual],
        "residual_zero_after_substitution": all(sp.simplify(item) == 0 for item in residual),
        "closure_conditions": closure_conditions,
        "still_open": still_open,
        "dust_monoflux_branch_required": True,
        "action_derivation_supplied": False,
        "same_phi_l_dynamically_selected": False,
        "dl_dlogb_residuals_closed": False,
        "mirror_residuals_closed": False,
        "uses_observational_fit": False,
        "conditional_cuu_closure": True,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "The projected Cuu identity closes algebraically on the cold monoflux dust branch "
            "once E_alpha=rho C_alpha(u,u) is available. This is a conditional bridge, not a "
            "derivation of the Janus action, L selection, or both residual closures."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Dust Monoflux Cuu Conditional Closure",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Projected residual: `{payload['projected_residual']}`",
        f"Residual zero after substitution: {payload['residual_zero_after_substitution']}",
        f"Dust monoflux branch required: {payload['dust_monoflux_branch_required']}",
        f"Action derivation supplied: {payload['action_derivation_supplied']}",
        f"Same phi/L dynamically selected: {payload['same_phi_l_dynamically_selected']}",
        f"DL/DlogB residuals closed: {payload['dl_dlogb_residuals_closed']}",
        f"Mirror residuals closed: {payload['mirror_residuals_closed']}",
        f"Conditional Cuu closure: {payload['conditional_cuu_closure']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Closure Conditions",
        "",
    ]
    lines.extend(f"- {item}" for item in payload["closure_conditions"])
    lines.extend(["", "## Still Open", ""])
    lines.extend(f"- {item}" for item in payload["still_open"])
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
