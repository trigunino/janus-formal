from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))


REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_core_action_radius_stationarity_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_core_action_radius_stationarity_gate.json"
)


def build_payload() -> dict:
    return {
        "status": "janus-z2-sigma-core-action-radius-stationarity-gate",
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_symbolic_derivation",
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_reuse_used": False,
        "archived_z4_background_reuse_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "observational_H0_fit_used": False,
        "observational_curvature_fit_used": False,
        "fitted_counterterm_coefficient_used": False,
        "round_sigma_geometry": {
            "sqrt_abs_h": "R^3 sqrt(det q)",
            "R_intrinsic": "6/R^2",
        },
        "density_family": {
            "L_core": "A sqrt(R_intrinsic) + B + C R_intrinsic",
            "A_fixed_by_Cartan_cancellation": "-3 epsilon_Z2/(sqrt(6) kappa_Z2Sigma)",
            "B_status": "unfixed throat tension or defect vacuum energy",
            "C_status": "unfixed intrinsic-curvature stiffness",
        },
        "stationarity_after_A_fixing": {
            "E_RSigma_remaining": "3 B R^2 + 6 C",
            "finite_positive_radius_condition": "R^2 = -2 C / B",
            "finite_positive_radius_requires": "B and C nonzero with opposite signs",
        },
        "routes": {
            "pure_tension_only": {
                "B_nonzero": True,
                "C_nonzero": False,
                "finite_positive_R": False,
                "reason": "stationarity gives R=0",
            },
            "pure_intrinsic_R_only": {
                "B_nonzero": False,
                "C_nonzero": True,
                "finite_positive_R": False,
                "reason": "stationarity requires C=0",
            },
            "tension_plus_intrinsic_R": {
                "B_nonzero": True,
                "C_nonzero": True,
                "finite_positive_R": True,
                "reason": "finite radius exists only if an action derives the ratio C/B",
            },
        },
        "closure_result": {
            "finite_radius_mechanism_identified": True,
            "R_Sigma_of_a_fixed_without_extra_coefficients": False,
            "needs_derived_ratio_C_over_B": True,
            "rsigma_solution_certificate_can_be_emitted": False,
        },
        "gate_passed": True,
        "primary_blocker": "derive_core_action_ratio_C_over_B",
        "next_required": [
            "derive B and C from resolved Janus tunnel core action",
            "or derive quantized C/B from a regularity or flux condition",
            "do_not_fit_B_or_C_to_observations",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Core Action Radius Stationarity Gate",
        "",
        f"Gate passed: `{payload['gate_passed']}`",
        f"Primary blocker: `{payload['primary_blocker']}`",
        "",
        "## Stationarity",
        "- `E_RSigma_remaining = 3 B R^2 + 6 C` after `sqrt(R[h])` cancels Cartan-GHY.",
        "- finite positive `R^2 = -2 C/B` requires derived opposite-sign `B,C`.",
    ]
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
