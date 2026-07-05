from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z2_sigma_counterterm_boundary_action_functional_gate import (
    build_payload as build_boundary_action,
)


REPORT_PATH = Path(
    "outputs/reports/"
    "p0_eft_janus_z2_sigma_counterterm_variational_coefficient_formula.md"
)
JSON_PATH = Path(
    "outputs/reports/"
    "p0_eft_janus_z2_sigma_counterterm_variational_coefficient_formula.json"
)


def build_payload() -> dict:
    action = build_boundary_action()
    action_closed = bool(action["boundary_action_functional_closed"])
    formulas = {
        "delta_S_ct": (
            "delta S_ct = integral_Sigma sqrt_abs_h "
            "[(1/2 h^ab L_ct + partial L_ct/partial h_ab) delta h_ab "
            "+ (partial L_ct/partial K_ab) delta K_ab "
            "+ (partial L_ct/partial chi) delta chi "
            "+ (partial L_ct/partial T_A) delta T_A]"
        ),
        "R_h_ab": "-(1/2 h^ab L_ct + partial L_ct/partial h_ab)",
        "R_K_ab": "-partial L_ct/partial K_ab",
        "R_chi": "-partial L_ct/partial chi",
        "R_T_A": "-partial L_ct/partial T_A",
    }
    return {
        "status": "janus-z2-sigma-counterterm-variational-coefficient-formula",
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_reuse_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "fitted_counterterm_coefficient_used": False,
        "boundary_action_functional_closed": action_closed,
        "measure_variation_included": action_closed,
        "residual_convention": "R = - delta L_density / delta field, including sqrt_abs_h measure term for h",
        "formulas": formulas,
        "formula_derivation_closed": action_closed,
        "explicit_values_ready": False,
        "counterterm_local_density_action_inputs_allowed": False,
        "primary_blocker": "explicit_L_ct_expression",
        "next_required": [
            "derive_explicit_L_ct_expression_in_allowed_basis",
            "evaluate_partial_L_ct_partial_h_ab",
            "evaluate_partial_L_ct_partial_K_ab",
            "then_write_counterterm_local_density_action_inputs_json",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Counterterm Variational Coefficient Formula",
        "",
        f"Formula derivation closed: `{payload['formula_derivation_closed']}`",
        f"Explicit values ready: `{payload['explicit_values_ready']}`",
        "",
        "## Formulas",
    ]
    for key, value in payload["formulas"].items():
        lines.append(f"- `{key}`: `{value}`")
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
