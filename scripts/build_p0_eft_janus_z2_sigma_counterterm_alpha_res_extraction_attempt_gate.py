from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z2_sigma_counterterm_residual_channel_frontier_gate import (
    build_payload as build_channel_frontier,
)
from scripts.derive_p0_eft_janus_z2_sigma_counterterm_residual_coefficients_partial import (
    build_payload as build_partial_coefficients,
)
from scripts.derive_p0_eft_janus_z2_sigma_counterterm_variational_coefficient_formula import (
    build_payload as build_variational_formula,
)
from scripts.build_p0_eft_janus_z2_sigma_counterterm_tetrad_residual_value_extraction_attempt_gate import (
    build_payload as build_tetrad_value_attempt,
)


REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_counterterm_alpha_res_extraction_attempt_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_counterterm_alpha_res_extraction_attempt_gate.json"
)
OUTPUT_PATH = Path("outputs/active_z2_sigma/counterterm_alpha_res_partial.json")


def build_payload(*, output_path: Path = OUTPUT_PATH) -> dict:
    frontier = build_channel_frontier()
    partial = build_partial_coefficients()
    formula = build_variational_formula()
    tetrad_value_attempt = build_tetrad_value_attempt()
    coeff = partial["coefficients"]
    partial_alpha = {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "alpha_res_status": "partial",
        "known_terms": {
            "torsion_pullback": "R_T^A dT_A = 0 on active torsionless branch",
            "immirzi_radial_contraction": "R_chi partial_R chi = 0",
        },
        "formal_terms": {
            "R_h_ab": formula["formulas"]["R_h_ab"],
            "R_K_ab": formula["formulas"]["R_K_ab"],
            "R_chi": formula["formulas"]["R_chi"],
        },
        "missing_terms": [
            "explicit_R_h_ab_values",
            "explicit_R_K_ab_values",
            "full_R_chi_value_if_nonradial_variation_needed",
            "connection_spinor_embedding_matter_channel_coefficients",
        ],
    }
    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_text(json.dumps(partial_alpha, indent=2), encoding="utf-8")
    all_explicit = frontier["channels"]["all_residual_channels_explicit"]
    return {
        "status": "janus-z2-sigma-counterterm-alpha-res-extraction-attempt-gate",
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_reuse_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "fitted_counterterm_coefficient_used": False,
        "alpha_res_partial_written": True,
        "alpha_res_output_manifest": str(output_path),
        "alpha_res_explicit": all_explicit,
        "nearest_residual_channel_frontier": frontier["nearest_residual_channel_frontier"],
        "known_partial_coefficients": {
            "R_T_A_ready": coeff.get("R_T_A_ready", False),
            "R_chi_partial_R_chi_ready": coeff.get("R_chi_partial_R_chi_ready", False),
        },
        "primary_blocker": frontier["primary_blocker"],
        "tetrad_value_extraction": {
            "R_h_ab_value_extractable": tetrad_value_attempt["R_h_ab_value_extractable"],
            "R_K_ab_value_extractable": tetrad_value_attempt["R_K_ab_value_extractable"],
            "primary_blocker": tetrad_value_attempt["primary_blocker"],
        },
        "partial_alpha_res": partial_alpha,
        "next_required": [
            "derive_tetrad_R_h_ab_R_K_ab_from_explicit_L_ct_or_boundary_residual",
            "close_connection_spinor_embedding_matter_residual_channels",
            "then_run_residual_one_form_decomposition_gate",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Counterterm Alpha Residual Extraction Attempt Gate",
        "",
        f"Partial alpha written: `{payload['alpha_res_partial_written']}`",
        f"Alpha explicit: `{payload['alpha_res_explicit']}`",
        f"Primary blocker: `{payload['primary_blocker']}`",
        "",
        "## Next Required",
    ]
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
