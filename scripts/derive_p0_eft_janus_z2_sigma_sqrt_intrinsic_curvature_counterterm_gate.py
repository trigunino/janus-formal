from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_sqrt_intrinsic_curvature_counterterm_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_sqrt_intrinsic_curvature_counterterm_gate.json"
)


def build_payload(*, dimension: int = 3) -> dict:
    if dimension != 3:
        raise ValueError("sqrt intrinsic-curvature closure is derived here only for dim Sigma = 3")
    return {
        "status": "janus-z2-sigma-sqrt-intrinsic-curvature-counterterm-gate",
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_symbolic_derivation",
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_reuse_used": False,
        "archived_z4_background_reuse_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "observational_H0_fit_used": False,
        "observational_curvature_fit_used": False,
        "fitted_counterterm_coefficient_used": False,
        "dimension": dimension,
        "round_sigma_geometry": {
            "h_ab": "R_Sigma^2 q_ab",
            "R_intrinsic": "6/R_Sigma^2",
            "sqrt_abs_h": "R_Sigma^3 sqrt(det q)",
        },
        "counterterm_density": {
            "L_ct": "A * sqrt(R_intrinsic)",
            "A_required": "-3 epsilon_Z2/(sqrt(6) kappa_Z2Sigma)",
            "L_ct_reduced": "-3 epsilon_Z2/(kappa_Z2Sigma R_Sigma)",
        },
        "radial_variation": {
            "partial_R_sqrt_h_L_ct": "-6 epsilon_Z2 sqrt(det q) R_Sigma/kappa_Z2Sigma",
            "E_CartanGHY_round": "+6 epsilon_Z2 sqrt(det q) R_Sigma/kappa_Z2Sigma",
            "E_counterterm_plus_E_CartanGHY": "0",
        },
        "closure_result": {
            "counterterm_cancels_CartanGHY_for_any_positive_R": True,
            "R_Sigma_solution_unique": False,
            "R_Sigma_of_a_fixed": False,
            "rsigma_solution_certificate_can_be_emitted": False,
        },
        "interpretation": (
            "The non-polynomial intrinsic density sqrt(R[h]) supplies the missing 1/R "
            "scaling and cancels the round Sigma Cartan-GHY radial block without fit. "
            "It also makes the throat radius a flat direction unless an additional "
            "physical condition fixes R_Sigma(a)."
        ),
        "gate_passed": True,
        "primary_blocker": "R_Sigma_modulus_not_fixed",
        "next_required": [
            "derive_boundary_condition_that_fixes_R_Sigma_modulus",
            "or_accept_scale_modulus_and_reformulate_certificate_as_flat_direction",
            "do_not_claim_no_fit_R_Sigma_of_a_from_this_counterterm_alone",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma sqrt(R[h]) Counterterm Gate",
        "",
        f"Gate passed: `{payload['gate_passed']}`",
        f"Primary blocker: `{payload['primary_blocker']}`",
        "",
        "## Result",
        "- `L_ct = -3 epsilon_Z2/(kappa_Z2Sigma R_Sigma)` on round Sigma.",
        "- `E_counterterm + E_CartanGHY = 0` for any positive `R_Sigma`.",
        "- `R_Sigma(a)` remains an unfixed modulus.",
    ]
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
