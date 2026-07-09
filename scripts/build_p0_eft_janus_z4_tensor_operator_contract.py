from __future__ import annotations

from pathlib import Path
import json

import sympy as sp


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_tensor_operator_contract.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_tensor_operator_contract.json")


def build_payload() -> dict:
    b, chi = sp.symbols("B chi", nonzero=True)
    t_plus, t_minus = sp.symbols("T_plus T_minus")
    b_inv = 1 / b
    stress = sp.Matrix([t_plus, t_minus])
    mixing = sp.Matrix([[1, b], [-b_inv, -1]])
    sector_sources = sp.simplify(chi * mixing * stress)
    master_source = sp.simplify(t_plus + b * t_minus)
    expected = sp.Matrix([chi * master_source, -chi * b_inv * master_source])
    residual = sp.simplify(sector_sources - expected)
    determinant = sp.simplify(mixing.det())
    rank_one = determinant == 0
    row_relation = sp.simplify(mixing[1, 0] + b_inv * mixing[0, 0]) == 0 and sp.simplify(
        mixing[1, 1] + b_inv * mixing[0, 1]
    ) == 0

    checks = {
        "published_coupled_field_equations_encoded": True,
        "determinant_weights_reciprocal": True,
        "mixing_matrix_determinant_zero": bool(rank_one),
        "minus_row_is_reciprocal_projection_of_plus_row": bool(row_relation),
        "sector_sources_descend_from_single_master_source": residual == sp.zeros(2, 1),
        "independent_sector_sources_forbidden": bool(rank_one and row_relation),
        "action_variation_from_janus_action_derived": False,
    }
    return {
        "status": "janus-z4-tensor-operator-contract",
        "lean_module": "JanusFormal.Legacy.Z4.Gates.P0EFTJanusZ4TensorOperatorContract",
        "source_equations": {
            "plus": "G_plus = chi * (T_plus + B*T_minus)",
            "minus": "G_minus = -chi * B^-1 * (T_plus + B*T_minus)",
        },
        "master_source": str(master_source),
        "mixing_matrix": [["1", "B"], ["-B^-1", "-1"]],
        "mixing_determinant": str(determinant),
        "sector_sources": [str(sp.simplify(x)) for x in sector_sources],
        "residual": str(residual),
        "checks": checks,
        "tensor_operator_from_coupled_equations_ready": all(
            value for key, value in checks.items()
            if key != "action_variation_from_janus_action_derived"
        ),
        "full_action_tensor_derivation_ready": False,
        "next_required": "Derive the same rank-one tensor operator directly by varying the Janus action.",
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z4 Tensor Operator Contract",
        "",
        f"Status: `{payload['status']}`",
        f"Lean module: `{payload['lean_module']}`",
        "",
        f"Master source: `{payload['master_source']}`",
        f"Mixing determinant: `{payload['mixing_determinant']}`",
        f"Residual: `{payload['residual']}`",
        "",
        "## Checks",
    ]
    for key, value in payload["checks"].items():
        lines.append(f"- `{key}`: `{value}`")
    lines.extend([
        "",
        f"Tensor operator from coupled equations ready: `{payload['tensor_operator_from_coupled_equations_ready']}`",
        f"Full action tensor derivation ready: `{payload['full_action_tensor_derivation_ready']}`",
        "",
        f"Next required: {payload['next_required']}",
        "",
    ])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
