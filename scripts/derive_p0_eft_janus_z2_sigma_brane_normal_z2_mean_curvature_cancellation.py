from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_brane_normal_z2_mean_curvature_cancellation.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_brane_normal_z2_mean_curvature_cancellation.json"
)


def build_payload() -> dict:
    formulas = {
        "brane_normal_equation": "barT_Sigma^{ab} Kbar_ab^rho = f_perp^rho",
        "mean_curvature": "Kbar_ab = (K_ab^+ + K_ab^-)/2",
        "z2_mirror_condition": "K_ab^- = - K_ab^+",
        "mean_curvature_under_z2": "Kbar_ab = 0",
        "left_hand_side_under_z2": "barT_Sigma^{ab} Kbar_ab^rho = 0",
        "m30_bulk_force_under_z2": "f_perp^rho = 0",
    }
    closure = {
        "Battye_Carter_Z2_trivial_force_condition_used": True,
        "Carter_mean_curvature_normal_equation_used": True,
        "Z2_normal_orientation_reversal_used": True,
        "K_minus_equals_minus_K_plus_declared": True,
        "mean_curvature_cancels": True,
        "normal_force_equation_closes_symbolically": True,
        "requires_DeltaK_values": False,
        "requires_defect_action": False,
    }
    return {
        "status": "janus-z2-sigma-brane-normal-z2-mean-curvature-cancellation",
        "active_core": "Z2_tunnel_Sigma",
        "formulas": formulas,
        "closure": closure,
        "gate_passed": bool(
            closure["mean_curvature_cancels"]
            and closure["normal_force_equation_closes_symbolically"]
            and not closure["requires_DeltaK_values"]
            and not closure["requires_defect_action"]
        ),
        "consequence": {
            "source_force_equation_closed_for_strict_Z2_transparent_branch": True,
            "tunnel_defect_forced_by_normal_brane_equation": False,
            "DeltaK_still_needed_for_junction_rho_p_and_RSigma": True,
        },
        "verdict": (
            "For a strict Z2 mirror throat, the mean extrinsic curvature in the "
            "Battye-Carter/Carter normal brane equation vanishes. Since the M30 bulk "
            "force also cancels by Z2 descent, the normal source-force equation closes "
            "symbolically without deriving DeltaK values. DeltaK remains needed for "
            "junction stress and R_Sigma, not for forcing a tunnel defect."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# Janus Z2/Sigma Brane Normal Z2 Mean-Curvature Cancellation",
        "",
        f"Gate passed: `{payload['gate_passed']}`",
        "",
        payload["verdict"],
        "",
        "## Formulas",
    ]
    lines.extend(f"- `{key}`: `{value}`" for key, value in payload["formulas"].items())
    return "\n".join(lines)


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(render_markdown(payload), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
