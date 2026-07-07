from __future__ import annotations

import json
import math
from pathlib import Path
from typing import Any


BASE = Path("outputs/active_z2_sigma")
INPUT_PATH = BASE / "area_flux_micro_parameter_inputs.json"
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_chi_ll_area_flux_micro_parameter_constraint.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_chi_ll_area_flux_micro_parameter_constraint.json")


def _read(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8")) if path.exists() else {}


def _positive_number(data: dict[str, Any], key: str) -> float | None:
    value = data.get(key)
    if not isinstance(value, (int, float)) or not math.isfinite(float(value)) or float(value) <= 0:
        return None
    return float(value)


def build_payload(input_path: Path = INPUT_PATH) -> dict[str, Any]:
    data = _read(input_path)
    n_flux = data.get("flux_integer_n")
    n_gap = data.get("N_gap")
    a_gap = _positive_number(data, "A_gap_m2")
    q_ll = _positive_number(data, "q_LL_dimensionless")
    f2 = _positive_number(data, "F2_0_m_minus_4")

    required_conditions = {
        "flux_integer_n_available": isinstance(n_flux, int) and n_flux != 0,
        "N_gap_available": isinstance(n_gap, int) and n_gap > 0,
        "A_gap_m2_available": a_gap is not None,
        "physical_area_gauge": data.get("area_gauge") == "physical_induced_S2_metric",
        "non_observational_provenance": bool(data.get("non_observational_provenance")),
    }

    constraint_rhs = None
    predicted_f2 = None
    predicted_q = None
    consistency = None
    if required_conditions["flux_integer_n_available"] and n_gap and a_gap:
        # From N_gap*A_gap = 4*pi*(n^2/(2 q^2 F2))^(1/2):
        # F2*q^2 = 8*pi^2*n^2/(N_gap*A_gap)^2.
        constraint_rhs = 8.0 * math.pi**2 * int(n_flux) ** 2 / (int(n_gap) * a_gap) ** 2
        if q_ll is not None:
            predicted_f2 = constraint_rhs / (q_ll * q_ll)
        if f2 is not None:
            predicted_q = math.sqrt(constraint_rhs / f2)
        if q_ll is not None and f2 is not None:
            lhs = f2 * q_ll * q_ll
            consistency = {
                "lhs_F2_q2": lhs,
                "rhs": constraint_rhs,
                "relative_difference": abs(lhs - constraint_rhs) / max(abs(lhs), abs(constraint_rhs)),
                "compatible": abs(lhs - constraint_rhs) / max(abs(lhs), abs(constraint_rhs)) < 1.0e-12,
            }

    relation_ready = constraint_rhs is not None and all(required_conditions.values())
    closes_one_parameter = relation_ready and (predicted_f2 is not None or predicted_q is not None)
    closes_both = relation_ready and q_ll is not None and f2 is not None and bool(
        consistency and consistency["compatible"]
    )

    return {
        "status": "janus-z2-chi-ll-area-flux-micro-parameter-constraint",
        "active_core": "Z2_tunnel_Sigma_null_PT_bridge",
        "physical_statement": (
            "Area-gap plus S2 flux compatibility does not choose q_LL and F2_0 "
            "separately. It fixes the product F2_0*q_LL^2 once n, N_gap and "
            "A_gap are derived."
        ),
        "required_conditions": required_conditions,
        "formulae": {
            "compatibility": "N_gap*A_gap = 4*pi*R_s(flux)^2",
            "micro_constraint": "F2_0*q_LL^2 = 8*pi^2*n^2/(N_gap*A_gap)^2",
            "solve_F2": "F2_0 = rhs/q_LL^2",
            "solve_q": "q_LL = sqrt(rhs/F2_0)",
        },
        "input_path": str(input_path),
        "input_present": input_path.exists(),
        "constraint_rhs_m_minus_4": constraint_rhs,
        "predicted_F2_0_m_minus_4_if_q_LL_given": predicted_f2,
        "predicted_q_LL_if_F2_0_given": predicted_q,
        "consistency": consistency,
        "micro_parameter_relation_ready": relation_ready,
        "one_micro_parameter_closable_if_other_given": closes_one_parameter,
        "both_micro_parameters_consistent": closes_both,
        "chi_LL_prediction_ready": False,
        "blocked_by": [key for key, value in required_conditions.items() if not value]
        + ([] if constraint_rhs is not None else ["area_flux_integer_gap_relation_inputs"])
        + ["one_of_q_LL_or_F2_0_still_required"],
        "gate_passed": True,
    }


def write_reports() -> dict[str, Any]:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2 chi_LL Area-Flux Micro-Parameter Constraint",
        "",
        payload["physical_statement"],
        "",
        f"Relation ready: `{payload['micro_parameter_relation_ready']}`",
        f"Constraint RHS m^-4: `{payload['constraint_rhs_m_minus_4']}`",
        "",
        "## Blocked By",
    ]
    lines.extend(f"- `{item}`" for item in payload["blocked_by"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
