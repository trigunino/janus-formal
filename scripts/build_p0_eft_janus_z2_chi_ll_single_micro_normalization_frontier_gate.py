from __future__ import annotations

import json
import math
from pathlib import Path
from typing import Any


BASE = Path("outputs/active_z2_sigma")
INPUT_PATH = BASE / "single_micro_normalization_inputs.json"
REPORT_PATH = Path(
    "outputs/reports/"
    "p0_eft_janus_z2_chi_ll_single_micro_normalization_frontier_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/"
    "p0_eft_janus_z2_chi_ll_single_micro_normalization_frontier_gate.json"
)


def _read(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8")) if path.exists() else {}


def _positive_number(data: dict[str, Any], key: str) -> float | None:
    value = data.get(key)
    if not isinstance(value, (int, float)):
        return None
    value = float(value)
    if not math.isfinite(value) or value <= 0.0:
        return None
    return value


def _positive_int(data: dict[str, Any], key: str) -> int | None:
    value = data.get(key)
    if not isinstance(value, int) or value <= 0:
        return None
    return value


def build_payload(input_path: Path = INPUT_PATH) -> dict[str, Any]:
    data = _read(input_path)
    n_flux = data.get("flux_integer_n")
    n_gap = _positive_int(data, "N_gap")
    a_gap = _positive_number(data, "A_gap_m2")
    p = _positive_number(data, "power_p")
    q_ll = _positive_number(data, "q_LL_dimensionless")
    lam = _positive_number(data, "lambda_F2")

    required_conditions = {
        "flux_integer_n_available": isinstance(n_flux, int) and n_flux != 0,
        "N_gap_available": n_gap is not None,
        "A_gap_m2_available": a_gap is not None,
        "power_p_available": p is not None,
        "physical_area_gauge": data.get("area_gauge") == "physical_induced_S2_metric",
        "non_observational_provenance": bool(data.get("non_observational_provenance")),
    }

    c_area = None
    if required_conditions["flux_integer_n_available"] and n_gap and a_gap:
        c_area = 8.0 * math.pi**2 * int(n_flux) ** 2 / (n_gap * a_gap) ** 2

    f2_from_q = c_area / (q_ll * q_ll) if c_area is not None and q_ll is not None else None
    lambda_from_q = (
        1.0 / (8.0 * p * f2_from_q**p)
        if f2_from_q is not None and p is not None
        else None
    )
    f2_from_lambda = (
        (0.125 / (lam * p)) ** (1.0 / p)
        if lam is not None and p is not None
        else None
    )
    q_from_lambda = (
        math.sqrt(c_area / f2_from_lambda)
        if c_area is not None and f2_from_lambda is not None
        else None
    )

    pair_consistency = None
    if q_ll is not None and lam is not None and c_area is not None and p is not None:
        f2_q = c_area / (q_ll * q_ll)
        f2_lam = (0.125 / (lam * p)) ** (1.0 / p)
        diff = abs(f2_q - f2_lam) / max(abs(f2_q), abs(f2_lam))
        pair_consistency = {
            "F2_from_q_LL": f2_q,
            "F2_from_lambda_F2": f2_lam,
            "relative_difference": diff,
            "compatible": diff < 1.0e-12,
        }

    invariant_lambda_over_q = (
        1.0 / (8.0 * p * c_area**p)
        if c_area is not None and p is not None
        else None
    )

    relation_ready = all(required_conditions.values()) and c_area is not None
    q_route_ready = relation_ready and q_ll is not None
    lambda_route_ready = relation_ready and lam is not None
    one_parameter_family = relation_ready and not (q_route_ready or lambda_route_ready)
    closed_if_pair_consistent = bool(pair_consistency and pair_consistency["compatible"])

    return {
        "status": "janus-z2-chi-ll-single-micro-normalization-frontier",
        "active_core": "Z2_tunnel_Sigma_null_PT_bridge",
        "physical_statement": (
            "Combining area-flux compatibility with the LL gauge action reduces "
            "the UV normalization to one micro choice. If q_LL is derived, "
            "lambda_F2 is fixed. If lambda_F2 is derived, q_LL is fixed. If "
            "neither is derived, chi_LL remains a one-parameter UV family."
        ),
        "input_path": str(input_path),
        "input_present": input_path.exists(),
        "required_conditions": required_conditions,
        "formulae": {
            "area_flux": "F2_0*q_LL^2 = 8*pi^2*n^2/(N_gap*A_gap)^2",
            "LL_action": "F2_0 = (1/(8*lambda_F2*p))^(1/p)",
            "lambda_from_q": "lambda_F2 = 1/(8*p*(C_area/q_LL^2)^p)",
            "q_from_lambda": "q_LL = sqrt(C_area/F2_0(lambda_F2,p))",
            "rescaling_invariant": "lambda_F2/q_LL^(2*p) = 1/(8*p*C_area^p)",
        },
        "C_area_m_minus_4": c_area,
        "invariant_lambda_F2_over_q_LL_2p": invariant_lambda_over_q,
        "gauge_normalization_rescaling": {
            "A_LL_to_s_A_LL": "F2_0 -> s^2 F2_0",
            "q_LL_to_q_LL_over_s": "keeps integral_S2 F_LL = 2*pi*n/q_LL covariant",
            "lambda_F2_to_lambda_F2_over_s_2p": "keeps L=lambda_F2*F2^p normalization covariant",
            "conclusion": (
                "Flux topology plus monomial action fixes lambda_F2/q_LL^(2p), "
                "not q_LL itself. A charge unit or action normalization is still "
                "a physical input, not a convention-free theorem."
            ),
        },
        "predicted_F2_0_m_minus_4_if_q_LL_given": f2_from_q,
        "predicted_lambda_F2_if_q_LL_given": lambda_from_q,
        "predicted_F2_0_m_minus_4_if_lambda_F2_given": f2_from_lambda,
        "predicted_q_LL_if_lambda_F2_given": q_from_lambda,
        "pair_consistency": pair_consistency,
        "single_micro_relation_ready": relation_ready,
        "q_LL_route_predicts_lambda_F2": q_route_ready,
        "lambda_F2_route_predicts_q_LL": lambda_route_ready,
        "one_parameter_UV_family_remaining": one_parameter_family,
        "both_micro_inputs_consistent": closed_if_pair_consistent,
        "chi_LL_prediction_ready": False,
        "blocked_by": [key for key, value in required_conditions.items() if not value]
        + (
            []
            if q_route_ready or lambda_route_ready
            else ["derive_q_LL_or_lambda_F2_from_Janus_UV_completion"]
        ),
        "forbidden_shortcuts": [
            "choose_q_LL_by_observation",
            "choose_lambda_F2_by_observation",
            "choose_flux_integer_by_observation",
            "choose_area_gap_occupation_by_observation",
        ],
        "gate_passed": True,
    }


def write_reports() -> dict[str, Any]:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2 chi_LL Single Micro-Normalization Frontier Gate",
        "",
        payload["physical_statement"],
        "",
        f"Single micro relation ready: `{payload['single_micro_relation_ready']}`",
        f"q_LL route predicts lambda_F2: `{payload['q_LL_route_predicts_lambda_F2']}`",
        f"lambda_F2 route predicts q_LL: `{payload['lambda_F2_route_predicts_q_LL']}`",
        f"One-parameter UV family remaining: `{payload['one_parameter_UV_family_remaining']}`",
        "",
        "## Blocked By",
    ]
    lines.extend(f"- `{item}`" for item in payload["blocked_by"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
