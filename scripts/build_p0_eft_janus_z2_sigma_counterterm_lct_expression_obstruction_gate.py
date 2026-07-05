from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z2_sigma_counterterm_residual_extraction_gate import (
    build_payload as build_residual_extraction,
)
from scripts.derive_p0_eft_janus_z2_sigma_counterterm_variational_coefficient_formula import (
    build_payload as build_variational_formula,
)
from scripts.build_p0_eft_janus_z2_sigma_counterterm_alpha_res_extraction_attempt_gate import (
    build_payload as build_alpha_attempt,
)


REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_counterterm_lct_expression_obstruction_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_counterterm_lct_expression_obstruction_gate.json"
)
OBSTRUCTION_PATH = Path("outputs/active_z2_sigma/counterterm_lct_expression_obstruction.json")


def build_payload(*, obstruction_path: Path = OBSTRUCTION_PATH) -> dict:
    residual = build_residual_extraction()
    formula = build_variational_formula()
    alpha_attempt = build_alpha_attempt()
    blocked = not residual["closure"]["residual_one_form_explicit"]
    payload = {
        "status": "janus-z2-sigma-counterterm-lct-expression-obstruction-gate",
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_reuse_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "fitted_counterterm_coefficient_used": False,
        "S_ct_boundary_action_available": formula["boundary_action_functional_closed"],
        "variational_formula_available": formula["formula_derivation_closed"],
        "residual_one_form_explicit": residual["closure"]["residual_one_form_explicit"],
        "alpha_res_partial_written": alpha_attempt["alpha_res_partial_written"],
        "alpha_res_partial_manifest": alpha_attempt["alpha_res_output_manifest"],
        "residual_integrability_proved": residual["closure"]["residual_integrability_proved"],
        "counterterm_primitive_integrated": residual["closure"]["counterterm_primitive_integrated"],
        "L_ct_expression_derivable_now": not blocked,
        "counterterm_local_density_action_inputs_written": False,
        "primary_blocker": "explicit_residual_one_form_alpha_res"
        if blocked
        else "residual_integrability_or_primitive",
        "obstruction": (
            "An explicit L_ct expression cannot be derived from uniqueness alone. "
            "The active Sigma boundary action and variation formula are known, but "
            "alpha_res must be made explicit and proved exact before integrating "
            "L_ct in the allowed local basis."
        ),
        "forbidden_shortcuts": [
            "choose alpha/beta ansatz for L_ct",
            "reuse Cartan-GHY K term as counterterm",
            "reuse dust/matter pulled action as counterterm",
            "fit L_ct coefficients to observations",
        ],
        "next_required": [
            "extract_explicit_alpha_res_components_R_h_R_K_R_chi",
            "prove_field_space_exactness_d_alpha_res_zero",
            "integrate_L_ct_equals_minus_integral_alpha_res",
            "then_materialize_counterterm_local_density_action_inputs_json",
        ],
    }
    obstruction_path.parent.mkdir(parents=True, exist_ok=True)
    obstruction_path.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    return payload


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Counterterm L_ct Expression Obstruction Gate",
        "",
        f"L_ct expression derivable now: `{payload['L_ct_expression_derivable_now']}`",
        f"Primary blocker: `{payload['primary_blocker']}`",
        "",
        payload["obstruction"],
        "",
        "## Next Required",
    ]
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
