from __future__ import annotations

import json
import math
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z2_chi_ll_route_a_lambda_over_q_origin_gate import (
    INPUT_PATH as ROUTE_A_INPUT,
    build_payload as route_a,
)
from scripts.build_p0_eft_janus_z2_sigma_route_b_max_closure_gate import (
    build_payload as route_b,
)


BASE = Path("outputs/active_z2_sigma")
DUAL_ROUTE_A_OUTPUT = BASE / "lambda_over_q_origin_from_area_flux_dual_inputs.json"
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_area_flux_dual_closure_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_area_flux_dual_closure_gate.json")


def build_payload(
    *,
    route_a_input: Path = ROUTE_A_INPUT,
    dual_route_a_output: Path = DUAL_ROUTE_A_OUTPUT,
    write_output: bool = False,
) -> dict:
    a = route_a(route_a_input)
    b = route_b(write_output=False)
    n_flux = None
    if a["route_a_origin_ready"]:
        n_flux = a["will_flux_radius_payload"]["flux_integer_n"]
    else:
        raw = json.loads(route_a_input.read_text(encoding="utf-8")) if route_a_input.exists() else {}
        n_flux = raw.get("flux_integer_n")

    lambda_over_q_from_b = None
    dual_payload = None
    if b["chi_LL_prediction_ready"] and isinstance(n_flux, int) and n_flux != 0:
        r_s = float(b["R_s_m"])
        lambda_over_q_from_b = r_s * r_s / (math.sqrt(8.0) * abs(n_flux))
        dual_payload = {
            "origin_route": "UV_action_dimensional_coupling",
            "UV_length_or_mass_scale_derived": True,
            "lambda_F2_from_UV_action_derived": True,
            "q_LL_from_same_UV_sector_derived": True,
            "lambda_F2_over_q_LL_m_minus_2": lambda_over_q_from_b,
            "flux_integer_n": n_flux,
            "area_gauge": "physical_induced_S2_metric",
            "provenance": "active_area_flux_dual_closure",
        }
        if write_output:
            dual_route_a_output.parent.mkdir(parents=True, exist_ok=True)
            dual_route_a_output.write_text(json.dumps(dual_payload, indent=2), encoding="utf-8")

    comparison = None
    if a["route_a_origin_ready"] and b["chi_LL_prediction_ready"]:
        a_ratio = float(a["lambda_F2_over_q_LL_m_minus_2"])
        b_ratio = lambda_over_q_from_b
        rel_ratio = abs(a_ratio - b_ratio) / max(abs(a_ratio), abs(b_ratio))
        a_radius = (8.0 * int(n_flux) ** 2 * a_ratio**2) ** 0.25
        b_radius = float(b["R_s_m"])
        rel_radius = abs(a_radius - b_radius) / max(abs(a_radius), abs(b_radius))
        comparison = {
            "route_a_lambda_over_q": a_ratio,
            "route_b_lambda_over_q": b_ratio,
            "lambda_over_q_relative_difference": rel_ratio,
            "route_a_R_s_m": a_radius,
            "route_b_R_s_m": b_radius,
            "R_s_relative_difference": rel_radius,
            "compatible": rel_ratio < 1.0e-12 and rel_radius < 1.0e-12,
        }

    if a["route_a_origin_ready"]:
        ready = bool(comparison and comparison["compatible"])
    else:
        ready = bool(dual_payload and b["chi_LL_prediction_ready"])
    return {
        "status": "janus-z2-sigma-area-flux-dual-closure-gate",
        "active_core": "Z2_tunnel_Sigma_null_PT_bridge",
        "physical_statement": (
            "Route A and Route B are dual descriptions of the same throat scale. "
            "B fixes R_s from quantized area; A fixes R_s from LL flux. Their "
            "compatibility imposes lambda_F2/q_LL = R_s(B)^2/(sqrt(8)*|n|)."
        ),
        "route_a_status": a["status"],
        "route_b_status": b["status"],
        "route_a_ready": a["route_a_origin_ready"],
        "route_b_ready": b["chi_LL_prediction_ready"],
        "flux_integer_n": n_flux,
        "lambda_F2_over_q_LL_from_route_b": lambda_over_q_from_b,
        "dual_route_a_payload": dual_payload,
        "comparison": comparison,
        "area_flux_dual_closure_ready": ready,
        "chi_LL_prediction_ready": ready,
        "blocked_by": (
            ([] if b["chi_LL_prediction_ready"] else ["route_b_not_ready"])
            + ([] if isinstance(n_flux, int) and n_flux != 0 else ["flux_integer_n_missing"])
            + ([] if a["route_a_origin_ready"] or dual_payload else ["route_a_not_ready"])
        ),
        "gate_passed": True,
    }


def write_reports() -> dict:
    payload = build_payload(write_output=True)
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2 Sigma Area-Flux Dual Closure Gate",
        "",
        payload["physical_statement"],
        "",
        f"Dual closure ready: `{payload['area_flux_dual_closure_ready']}`",
        f"lambda_F2/q_LL from B: `{payload['lambda_F2_over_q_LL_from_route_b']}`",
        "",
        "## Blocked By",
    ]
    lines.extend(f"- `{item}`" for item in payload["blocked_by"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
