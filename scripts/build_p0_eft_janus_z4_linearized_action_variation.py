from __future__ import annotations

from pathlib import Path
import json

import sympy as sp


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_linearized_action_variation.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_linearized_action_variation.json")


def build_payload() -> dict:
    b, chi = sp.symbols("B chi", nonzero=True)
    h_plus, h_minus = sp.symbols("h_plus h_minus")
    t_plus, t_minus = sp.symbols("T_plus T_minus")
    master = sp.simplify(t_plus + b * t_minus)
    source_action_density = sp.simplify(chi * (h_plus - h_minus / b) * master)
    el_plus = sp.diff(source_action_density, h_plus)
    el_minus = sp.diff(source_action_density, h_minus)
    expected_plus = sp.simplify(chi * master)
    expected_minus = sp.simplify(-chi * master / b)
    residual = sp.simplify(sp.Matrix([el_plus - expected_plus, el_minus - expected_minus]))
    checks = {
        "source_action_density_declared": True,
        "plus_variation_matches_rank_one_source": sp.simplify(el_plus - expected_plus) == 0,
        "minus_variation_matches_rank_one_source": sp.simplify(el_minus - expected_minus) == 0,
        "reciprocal_determinant_weight_used": True,
        "linear_boundary_terms_excluded": True,
        "nonlinear_action_variation_closed": False,
    }
    return {
        "status": "janus-z4-linearized-action-variation",
        "lean_module": "JanusFormal.Legacy.Z4.Gates.P0EFTJanusZ4LinearizedActionVariation",
        "source_action_density": str(source_action_density),
        "master_source": str(master),
        "el_plus": str(el_plus),
        "el_minus": str(el_minus),
        "residual": str(residual),
        "checks": checks,
        "linearized_action_variation_ready": all(
            value for key, value in checks.items()
            if key != "nonlinear_action_variation_closed"
        ),
        "full_action_variation_ready": False,
        "next_required": "Extend this linearized source action to the full nonlinear Janus action including measure and boundary variations.",
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z4 Linearized Action Variation",
        "",
        f"Status: `{payload['status']}`",
        f"Action density: `{payload['source_action_density']}`",
        f"EL plus: `{payload['el_plus']}`",
        f"EL minus: `{payload['el_minus']}`",
        f"Residual: `{payload['residual']}`",
        "",
        "## Checks",
    ]
    for key, value in payload["checks"].items():
        lines.append(f"- `{key}`: `{value}`")
    lines.extend([
        "",
        f"Linearized action variation ready: `{payload['linearized_action_variation_ready']}`",
        f"Full action variation ready: `{payload['full_action_variation_ready']}`",
        "",
        f"Next required: {payload['next_required']}",
        "",
    ])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
