from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z2_sigma_projective_gluing_normal_orientation_sign_gate import (
    build_payload as build_orientation,
)
from scripts.build_p0_eft_janus_z2_sigma_equivariant_flux_cancellation_gate import (
    build_payload as build_flux_cancellation,
)
from scripts.build_p0_eft_janus_sigma_boundary_nonlinear_residual_closure_gate import (
    build_payload as build_nonlinear_closure,
)


REPORT_PATH = Path(
    "outputs/reports/"
    "p0_eft_janus_z2_sigma_counterterm_z2_odd_residual_projection_route_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/"
    "p0_eft_janus_z2_sigma_counterterm_z2_odd_residual_projection_route_gate.json"
)


def build_payload() -> dict:
    orientation = build_orientation()
    flux = build_flux_cancellation()
    nonlinear = build_nonlinear_closure()
    declared = {
        "Z2_orientation_reversal_available": orientation[
            "projective_gluing_normal_orientation_sign_ready"
        ],
        "Sigma_residual_projection_route_declared": True,
        "odd_residual_cancellation_condition_declared": True,
        "counterterm_density_bypass_requires_anti_invariance": True,
        "no_density_ansatz_used": True,
        "observational_fit_forbidden": True,
    }
    closure = {
        "nonlinear_residual_closure_available": nonlinear[
            "sigma_nonlinear_boundary_residual_closed"
        ],
        "alpha_res_components_available": nonlinear["component_emission"][
            "alpha_res_components_available"
        ],
        "alpha_res_Z2_anti_invariance_proved": False,
        "paired_sheet_residual_support_proved": flux["closure"].get(
            "Z2_equivariant_embedding_derived", False
        ),
        "quotient_projection_cancels_alpha_res": False,
        "E_counterterm_zero_without_density": False,
    }
    ready = all(declared.values()) and all(closure.values())
    return {
        "status": "janus-z2-sigma-counterterm-z2-odd-residual-projection-route-gate",
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_reuse_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "fitted_counterterm_coefficient_used": False,
        "declared": declared,
        "closure": closure,
        "route_formula": {
            "anti_invariance": "tau_Z2^* alpha_res = - alpha_res",
            "quotient_cancellation": "pi_* alpha_res = 0 on Sigma/Z2",
            "consequence": "E_counterterm = 0 without constructing L_ct",
        },
        "route_ready": ready,
        "gate_passed": ready,
        "primary_blocker": "alpha_res_Z2_anti_invariance"
        if not ready
        else "none",
        "interpretation": (
            "This is the only credible bypass of explicit L_ct found so far: "
            "Janus/Z2 geometry could make the residual odd under sheet exchange. "
            "The current repo has orientation reversal but not anti-invariance of "
            "the residual one-form, so the bypass remains blocked."
        ),
        "next_required": [
            "prove_tau_Z2_pullback_alpha_res_equals_minus_alpha_res",
            "prove_residual_support_is_paired_across_Sigma",
            "prove_quotient_projection_cancels_odd_residual",
            "then_set_E_counterterm_zero_or_return_to_L_ct_expression_route",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Counterterm Z2-Odd Residual Projection Route Gate",
        "",
        f"Route ready: `{payload['route_ready']}`",
        f"Primary blocker: `{payload['primary_blocker']}`",
        "",
        payload["interpretation"],
        "",
        "## Route Formula",
    ]
    lines.extend(f"- `{key}`: `{value}`" for key, value in payload["route_formula"].items())
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
