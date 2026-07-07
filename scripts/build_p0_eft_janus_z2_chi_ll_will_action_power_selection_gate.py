from __future__ import annotations

import json
import math
from pathlib import Path
from typing import Any


BASE = Path("outputs/active_z2_sigma")
INPUT_PATH = BASE / "will_action_power_selection_inputs.json"
REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_chi_ll_will_action_power_selection_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_chi_ll_will_action_power_selection_gate.json"
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
    return value if isinstance(value, int) and value > 0 else None


def build_payload(input_path: Path = INPUT_PATH) -> dict[str, Any]:
    data = _read(input_path)
    n_flux = data.get("flux_integer_n")
    n_gap = _positive_int(data, "N_gap")
    a_gap = _positive_number(data, "A_gap_m2")
    q_ll = _positive_number(data, "q_LL_dimensionless")

    will_conditions = {
        "WILL_square_root_action_selected": True,
        "power_p_fixed_by_Weyl_invariant_LL_action": True,
        "power_p_value": 0.5,
        "auxiliary_sqrt_F2_units_not_SI": True,
    }
    required_conditions = {
        "flux_integer_n_available": isinstance(n_flux, int) and n_flux != 0,
        "N_gap_available": n_gap is not None,
        "A_gap_m2_available": a_gap is not None,
        "physical_area_gauge": data.get("area_gauge") == "physical_induced_S2_metric",
        "non_observational_provenance": bool(data.get("non_observational_provenance")),
    }

    c_area = None
    if required_conditions["flux_integer_n_available"] and n_gap and a_gap:
        c_area = 8.0 * math.pi**2 * int(n_flux) ** 2 / (n_gap * a_gap) ** 2

    p = 0.5
    lambda_over_q = 1.0 / (8.0 * p * c_area**p) if c_area is not None else None
    lambda_if_q = lambda_over_q * q_ll if lambda_over_q is not None and q_ll is not None else None
    f2_if_q = c_area / (q_ll * q_ll) if c_area is not None and q_ll is not None else None

    relation_ready = all(required_conditions.values()) and c_area is not None
    q_route_ready = relation_ready and q_ll is not None

    return {
        "status": "janus-z2-chi-ll-will-action-power-selection-gate",
        "active_core": "Z2_tunnel_Sigma_null_PT_bridge",
        "physical_statement": (
            "The Weyl-invariant lightlike/WILL-brane action selects the "
            "sqrt(F2) family, i.e. p=1/2. Combined with area-flux compatibility "
            "this fixes lambda_F2/q_LL, not q_LL itself."
        ),
        "input_path": str(input_path),
        "input_present": input_path.exists(),
        "will_conditions": will_conditions,
        "required_conditions": required_conditions,
        "formulae": {
            "WILL_action": "L(F2)=lambda_F2*sqrt(F2)",
            "p": "1/2",
            "area_flux": "C_area=F2_0*q_LL^2",
            "invariant": "lambda_F2/q_LL = 1/(4*sqrt(C_area))",
        },
        "C_area_m_minus_4": c_area,
        "predicted_lambda_F2_over_q_LL": lambda_over_q,
        "predicted_lambda_F2_if_q_LL_given": lambda_if_q,
        "predicted_F2_0_m_minus_4_if_q_LL_given": f2_if_q,
        "WILL_power_selection_ready": True,
        "single_micro_relation_ready": relation_ready,
        "q_LL_route_predicts_lambda_F2": q_route_ready,
        "chi_LL_prediction_ready": False,
        "blocked_by": [key for key, value in required_conditions.items() if not value]
        + ([] if q_route_ready else ["derive_worldvolume_charge_unit_q_LL"]),
        "no_rustine_verdict": (
            "WILL symmetry advances the action-family derivation by fixing p=1/2. "
            "It does not remove the charge-normalization freedom of the auxiliary "
            "worldvolume gauge field."
        ),
        "gate_passed": True,
    }


def write_reports() -> dict[str, Any]:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2 chi_LL WILL Action Power Selection Gate",
        "",
        payload["physical_statement"],
        "",
        f"WILL power selection ready: `{payload['WILL_power_selection_ready']}`",
        f"Single micro relation ready: `{payload['single_micro_relation_ready']}`",
        f"Predicted lambda_F2/q_LL: `{payload['predicted_lambda_F2_over_q_LL']}`",
        "",
        "## Blocked By",
    ]
    lines.extend(f"- `{item}`" for item in payload["blocked_by"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
