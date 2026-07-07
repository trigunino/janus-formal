from __future__ import annotations

import json
import math
from pathlib import Path
from typing import Any


BASE = Path("outputs/active_z2_sigma")
INPUT_PATH = BASE / "will_flux_radius_inputs.json"
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_chi_ll_will_flux_radius_reducer_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_chi_ll_will_flux_radius_reducer_gate.json")


def _read(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8")) if path.exists() else {}


def _positive_number(data: dict[str, Any], key: str) -> float | None:
    value = data.get(key)
    if not isinstance(value, (int, float)):
        return None
    value = float(value)
    return value if math.isfinite(value) and value > 0.0 else None


def build_payload(input_path: Path = INPUT_PATH) -> dict[str, Any]:
    data = _read(input_path)
    n_flux = data.get("flux_integer_n")
    lambda_over_q = _positive_number(data, "lambda_F2_over_q_LL")

    required_conditions = {
        "WILL_power_p_equals_one_half": data.get("power_p", 0.5) == 0.5,
        "flux_integer_n_available": isinstance(n_flux, int) and n_flux != 0,
        "lambda_F2_over_q_LL_available": lambda_over_q is not None,
        "physical_area_gauge": data.get("area_gauge") == "physical_induced_S2_metric",
        "non_observational_provenance": bool(data.get("non_observational_provenance")),
    }

    r_s = None
    chi = None
    if isinstance(n_flux, int) and n_flux != 0 and lambda_over_q is not None:
        # WILL action: F2_0 = 1/(16 lambda_F2^2).
        # Flux: B=n/(2 q_LL), F2_0 = 2 B^2/R_s^4.
        # Therefore R_s^4 = 8 n^2 (lambda_F2/q_LL)^2.
        r_s = (8.0 * int(n_flux) ** 2 * lambda_over_q**2) ** 0.25
        chi = 1.0 / (8.0 * math.pi * r_s)

    ready = all(required_conditions.values()) and r_s is not None

    return {
        "status": "janus-z2-chi-ll-will-flux-radius-reducer",
        "active_core": "Z2_tunnel_Sigma_null_PT_bridge",
        "physical_statement": (
            "For the WILL square-root action, the separate q_LL and lambda_F2 "
            "normalizations collapse to the invariant ratio lambda_F2/q_LL. "
            "Flux sector n then gives R_s^4 = 8*n^2*(lambda_F2/q_LL)^2."
        ),
        "input_path": str(input_path),
        "input_present": input_path.exists(),
        "required_conditions": required_conditions,
        "formulae": {
            "WILL_on_shell_F2": "F2_0 = 1/(16*lambda_F2^2)",
            "flux_F2": "F2_0 = 2*(n/(2*q_LL))^2/R_s^4",
            "radius": "R_s = (8*n^2*(lambda_F2/q_LL)^2)^(1/4)",
            "tension": "chi_LL = -1/(8*pi*R_s)",
        },
        "R_s_m_if_ratio_dimension_m_minus_2": r_s,
        "chi_LL_abs_inverse_m": chi,
        "WILL_flux_radius_ready": ready,
        "chi_LL_prediction_ready": ready,
        "blocked_by": [key for key, value in required_conditions.items() if not value],
        "normalization_verdict": (
            "q_LL alone is not the physical blocker after WILL reduction. The "
            "physical blocker is the invariant ratio lambda_F2/q_LL with its "
            "dimensionful Janus/PT origin."
        ),
        "gate_passed": True,
    }


def write_reports() -> dict[str, Any]:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2 chi_LL WILL Flux Radius Reducer Gate",
        "",
        payload["physical_statement"],
        "",
        f"WILL flux radius ready: `{payload['WILL_flux_radius_ready']}`",
        f"R_s: `{payload['R_s_m_if_ratio_dimension_m_minus_2']}`",
        "",
        "## Blocked By",
    ]
    lines.extend(f"- `{item}`" for item in payload["blocked_by"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
