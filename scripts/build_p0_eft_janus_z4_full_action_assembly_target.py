from __future__ import annotations

from pathlib import Path
import json

import sympy as sp


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_full_action_assembly_target.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_full_action_assembly_target.json")


def build_payload() -> dict:
    B, chi = sp.symbols("B chi", nonzero=True)
    T_plus, T_minus = sp.symbols("T_plus T_minus")
    r_nl_plus, r_nl_minus = sp.symbols("R_nl_plus R_nl_minus")

    master = T_plus + B * T_minus
    target_plus = chi * master
    target_minus = -chi * master / B

    assembled_plus = target_plus + r_nl_plus
    assembled_minus = target_minus + r_nl_minus
    residual = sp.Matrix([
        sp.simplify(assembled_plus - target_plus),
        sp.simplify(assembled_minus - target_minus),
    ])

    return {
        "status": "janus-z4-full-action-assembly-target",
        "master_source": str(master),
        "target_el_plus": str(target_plus),
        "target_el_minus": str(target_minus),
        "assembled_el_plus": str(assembled_plus),
        "assembled_el_minus": str(assembled_minus),
        "nonlinear_residual": str(residual),
        "full_action_assembly_scaffold_ready": True,
        "z4_rank_one_source_recovered": residual == sp.Matrix([r_nl_plus, r_nl_minus]),
        "nonlinear_euler_lagrange_residual_vanishing": False,
        "full_action_variation_closed": False,
        "next_required": (
            "Derive R_nl_plus = 0 and R_nl_minus = 0 from the nonlinear "
            "determinant-coupled Z4 tetrad action."
        ),
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z4 Full Action Assembly Target",
        "",
        f"Status: `{payload['status']}`",
        f"Assembly scaffold ready: `{payload['full_action_assembly_scaffold_ready']}`",
        f"Rank-one source recovered: `{payload['z4_rank_one_source_recovered']}`",
        f"Nonlinear EL residual vanishing: `{payload['nonlinear_euler_lagrange_residual_vanishing']}`",
        f"Full action variation closed: `{payload['full_action_variation_closed']}`",
        "",
        "## Target",
        "",
        f"- master source: `{payload['master_source']}`",
        f"- target EL plus: `{payload['target_el_plus']}`",
        f"- target EL minus: `{payload['target_el_minus']}`",
        f"- nonlinear residual: `{payload['nonlinear_residual']}`",
        "",
        f"Next required: {payload['next_required']}",
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
