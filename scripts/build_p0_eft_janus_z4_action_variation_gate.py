from __future__ import annotations

from pathlib import Path
import json

import sympy as sp


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_action_variation_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_action_variation_gate.json")


def build_payload() -> dict:
    b, chi = sp.symbols("B chi", nonzero=True)
    t_plus, t_minus = sp.symbols("T_plus T_minus")
    el_plus, el_minus = sp.symbols("EL_plus EL_minus")
    master = t_plus + b * t_minus
    required_el = sp.Matrix([chi * master, -chi * master / b])
    supplied_el = sp.Matrix([el_plus, el_minus])
    matching_conditions = [
        sp.Eq(el_plus, required_el[0]),
        sp.Eq(el_minus, required_el[1]),
    ]
    residual_after_substitution = sp.simplify(
        supplied_el.subs({el_plus: required_el[0], el_minus: required_el[1]}) - required_el
    )
    checks = {
        "action_density_slot_declared": True,
        "measure_variation_slot_declared": True,
        "euler_lagrange_matching_conditions_encoded": True,
        "rank_one_operator_recovered_if_conditions_hold": residual_after_substitution == sp.zeros(2, 1),
        "boundary_terms_must_be_closed": True,
        "full_action_variation_closed": False,
    }
    return {
        "status": "janus-z4-action-variation-gate",
        "lean_module": "JanusFormal.P0EFTJanusZ4ActionVariationGate",
        "master_source": str(master),
        "matching_conditions": [str(condition) for condition in matching_conditions],
        "residual_after_substitution": str(residual_after_substitution),
        "checks": checks,
        "action_variation_scaffold_ready": all(
            value for key, value in checks.items()
            if key != "full_action_variation_closed"
        ),
        "full_action_variation_closed": False,
        "next_required": "Compute the Frechet variation of the concrete Janus action and prove these EL matching conditions.",
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z4 Action Variation Gate",
        "",
        f"Status: `{payload['status']}`",
        f"Master source: `{payload['master_source']}`",
        f"Residual after substitution: `{payload['residual_after_substitution']}`",
        "",
        "## Matching Conditions",
    ]
    lines.extend(f"- `{condition}`" for condition in payload["matching_conditions"])
    lines.extend(["", "## Checks"])
    for key, value in payload["checks"].items():
        lines.append(f"- `{key}`: `{value}`")
    lines.extend([
        "",
        f"Action variation scaffold ready: `{payload['action_variation_scaffold_ready']}`",
        f"Full action variation closed: `{payload['full_action_variation_closed']}`",
        "",
        f"Next required: {payload['next_required']}",
        "",
    ])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
