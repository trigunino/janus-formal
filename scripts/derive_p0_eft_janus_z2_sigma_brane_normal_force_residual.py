from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z2_sigma_tunnel_junction_flrw_reduction_gate import (
    build_payload as build_junction_flrw,
)
from scripts.derive_p0_eft_janus_z2_sigma_tunnel_defect_vs_transparency_decision import (
    build_payload as build_defect_decision,
)
from scripts.derive_p0_eft_janus_z2_sigma_brane_normal_z2_mean_curvature_cancellation import (
    build_payload as build_z2_mean_curvature,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_brane_normal_force_residual.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_brane_normal_force_residual.json")


def build_payload() -> dict:
    junction = build_junction_flrw()
    decision = build_defect_decision()
    z2_mean = build_z2_mean_curvature()
    formulas = {
        "normal_brane_equation": "barT_Sigma^{ab} Kbar_ab^rho = f_perp^rho",
        "mean_curvature": "Kbar_ab = (K_ab^+ + K_ab^-)/2",
        "isotropic_reduction": "F_normal = rho_Sigma Kbar_tau + 3 p_Sigma Kbar_s - f_perp",
        "junction_rho": junction["formulas"]["rho_junction"],
        "junction_p": junction["formulas"]["p_junction"],
        "strict_Z2_case": "f_perp = 0 and Z2-even S_ab, Z2-odd normal force",
        "defect_residual": "F_defect = rho_Sigma K_tau + 3 p_Sigma K_s",
    }
    inputs = {
        "junction_FLRW_algebra_ready": bool(junction["tunnel_junction_FLRW_algebra_ready"]),
        "DeltaK_s_of_a_ready": bool(junction["closure"]["DeltaK_s_of_a_ready"]),
        "DeltaK_tau_of_a_ready": bool(junction["closure"]["DeltaK_tau_of_a_ready"]),
        "junction_rho_p_of_a_ready": bool(junction["closure"]["junction_rho_p_of_a_ready"]),
        "strict_Z2_bulk_force_cancels": bool(
            decision["decision_criteria"]["strict_Z2_bulk_force_cancels"]
        ),
        "active_metric_embedding_available": bool(
            decision["decision_criteria"]["active_metric_embedding_available"]
        ),
    }
    residual_symbolic_ready = inputs["junction_FLRW_algebra_ready"]
    residual_values_ready = all(
        inputs[key]
        for key in (
            "DeltaK_s_of_a_ready",
            "DeltaK_tau_of_a_ready",
            "junction_rho_p_of_a_ready",
            "active_metric_embedding_available",
        )
    )
    strict_z2_closes_force = (
        bool(z2_mean["consequence"]["source_force_equation_closed_for_strict_Z2_transparent_branch"])
        and inputs["strict_Z2_bulk_force_cancels"]
    )
    return {
        "status": "janus-z2-sigma-brane-normal-force-residual",
        "active_core": "Z2_tunnel_Sigma",
        "bibliography_basis": [
            "Battye-Carter normal brane force condition",
            "Carter brane dynamics Tbar.K = f_perp",
            "Mars-Senovilla distributional Bianchi guard",
        ],
        "formulas": formulas,
        "inputs": inputs,
        "residual_symbolic_ready": residual_symbolic_ready,
        "residual_values_ready": residual_values_ready,
        "strict_Z2_mean_curvature_cancellation_ready": bool(z2_mean["gate_passed"]),
        "strict_Z2_closes_normal_force": strict_z2_closes_force,
        "defect_forced": False if not residual_values_ready else not strict_z2_closes_force,
        "gate_passed": residual_symbolic_ready,
        "primary_blocker": "none"
        if residual_values_ready
        else "DeltaK_s_of_a_ready",
        "next_required": [
            "derive active DeltaK_s(a), DeltaK_tau(a) from X_±(R_Sigma)",
            "compute rho_Sigma(a), p_Sigma(a) from non-circular junction partition",
            "evaluate F_normal(a)",
            "if F_normal=0 under strict Z2: close transparency branch",
            "if F_normal!=0: this residual is the required tunnel-defect source",
        ],
        "verdict": (
            "The source-force equation is instantiated as the brane normal dynamics "
            "residual. It is symbolically ready, but numerical/functional closure waits "
            "on active extrinsic-curvature jumps and surface stress partition."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# Janus Z2/Sigma Brane Normal Force Residual",
        "",
        f"Symbolic ready: `{payload['residual_symbolic_ready']}`",
        f"Values ready: `{payload['residual_values_ready']}`",
        f"Strict Z2 closes normal force: `{payload['strict_Z2_closes_normal_force']}`",
        f"Defect forced: `{payload['defect_forced']}`",
        "",
        payload["verdict"],
        "",
        "## Formulas",
    ]
    lines.extend(f"- `{key}`: `{value}`" for key, value in payload["formulas"].items())
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    return "\n".join(lines)


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(render_markdown(payload), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
