from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_sigma_boundary_nonlinear_residual_closure_gate import (
    build_payload as build_nonlinear_closure,
)
from scripts.build_p0_eft_janus_z2_sigma_counterterm_tetrad_residual_channel_gate import (
    build_payload as build_tetrad_channel,
)
from scripts.derive_p0_eft_janus_z2_sigma_counterterm_variational_coefficient_formula import (
    build_payload as build_formula,
)


REPORT_PATH = Path(
    "outputs/reports/"
    "p0_eft_janus_z2_sigma_counterterm_tetrad_residual_value_extraction_attempt_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/"
    "p0_eft_janus_z2_sigma_counterterm_tetrad_residual_value_extraction_attempt_gate.json"
)


def build_payload() -> dict:
    nonlinear = build_nonlinear_closure()
    tetrad = build_tetrad_channel()
    formula = build_formula()
    component_emission = nonlinear.get("component_emission", {})
    closure_has_values = bool(component_emission.get("alpha_res_component_values_available"))
    return {
        "status": "janus-z2-sigma-counterterm-tetrad-residual-value-extraction-attempt-gate",
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_reuse_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "fitted_counterterm_coefficient_used": False,
        "nonlinear_residual_closure_available": nonlinear[
            "sigma_nonlinear_boundary_residual_closed"
        ],
        "nonlinear_closure_is_boolean_only": nonlinear.get(
            "nonlinear_closure_is_boolean_only", not closure_has_values
        ),
        "component_emission": component_emission,
        "tetrad_transport_ready": tetrad["closure"]["tetrad_variation_transport_ready"],
        "variational_formula_available": formula["formula_derivation_closed"],
        "R_h_ab_value_extractable": False,
        "R_K_ab_value_extractable": False,
        "counterterm_metric_residual_tensor_inputs_written": False,
        "counterterm_extrinsic_residual_tensor_inputs_written": False,
        "primary_blocker": "nonlinear_closure_lacks_alpha_res_component_values",
        "obstruction": (
            "The active nonlinear Sigma residual closure proves cancellation/uniqueness "
            "and now exposes the alpha_res component schema, but it does not expose "
            "component values, L_ct_expression, R_h_ab, or R_K_ab. "
            "The tetrad transport and variational formulas are closed, so the remaining "
            "missing input is the explicit residual tensor data, not transport."
        ),
        "next_required": [
            "refine_sigma_boundary_nonlinear_residual_closure_to_emit_alpha_res_component_values",
            "derive_R_h_ab_R_K_ab_from_emitted_alpha_res_components",
            "then_run_residual_tensors_from_local_density_action",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Counterterm Tetrad Residual Value Extraction Attempt Gate",
        "",
        f"R_h extractable: `{payload['R_h_ab_value_extractable']}`",
        f"R_K extractable: `{payload['R_K_ab_value_extractable']}`",
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
