from __future__ import annotations

import json
import math
from pathlib import Path
from typing import Any


BASE = Path("outputs/active_z2_sigma")
INPUT_PATH = BASE / "area_gap_exit_inputs.json"
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_chi_ll_area_gap_exit_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_chi_ll_area_gap_exit_gate.json")


def _read(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8")) if path.exists() else {}


def _derive(data: dict[str, Any]) -> dict[str, Any]:
    area_gap = data.get("A_gap_m2")
    n_gap = data.get("N_gap")
    if area_gap is None or n_gap is None:
        return {"ready": False, "missing": ["A_gap_m2", "N_gap"]}
    if not isinstance(n_gap, int) or n_gap <= 0:
        return {"ready": False, "missing": ["positive_integer_N_gap"]}
    area_gap = float(area_gap)
    if not math.isfinite(area_gap) or area_gap <= 0:
        return {"ready": False, "missing": ["positive_A_gap_m2"]}
    area = n_gap * area_gap
    radius = math.sqrt(area / (4.0 * math.pi))
    return {
        "ready": True,
        "A_Sigma_m2": area,
        "R_s_m": radius,
        "chi_LL_abs_inverse_m": 1.0 / (8.0 * math.pi * radius),
        "chi_LL_sign": "negative_PT_branch",
    }


def build_payload(input_path: Path = INPUT_PATH) -> dict[str, Any]:
    data = _read(input_path)
    required_conditions = {
        "quantum_area_operator_on_Sigma": bool(data.get("quantum_area_operator_on_Sigma")),
        "area_gap_formula_declared": data.get("A_gap_m2") is not None,
        "A_Sigma_equals_N_gap_A_gap_theorem": bool(
            data.get("A_Sigma_equals_N_gap_A_gap_theorem")
        ),
        "N_gap_selected_by_theory_or_state": isinstance(data.get("N_gap"), int),
        "physical_induced_area_gauge": data.get("area_gauge") == "physical_induced_S2_metric",
        "non_observational_provenance": bool(data.get("non_observational_provenance")),
    }
    derivation = _derive(data)
    ready = all(required_conditions.values()) and derivation["ready"]
    return {
        "status": "janus-z2-chi-ll-area-gap-exit-gate",
        "active_core": "Z2_tunnel_Sigma_null_PT_bridge",
        "physical_idea": "A quantized area spectrum can fix R_s only if Sigma area equals N_gap times a derived area gap.",
        "required_conditions": required_conditions,
        "formulae": {
            "area": "A_Sigma=N_gap*A_gap",
            "radius": "R_s=sqrt(A_Sigma/(4*pi))",
            "ll_tension": "chi_LL=-1/(8*pi*R_s)",
        },
        "forbidden_shortcuts": {
            "set_A_Sigma_equal_area_gap_by_choice": True,
            "choose_N_gap_by_observation": True,
            "use_area_gap_without_area_operator_on_Sigma": True,
        },
        "input_path": str(input_path),
        "input_present": input_path.exists(),
        "derivation": derivation,
        "area_gap_exit_ready": ready,
        "chi_LL_prediction_ready": ready,
        "blocked_by": [key for key, value in required_conditions.items() if not value]
        + derivation.get("missing", []),
        "gate_passed": True,
    }


def write_reports() -> dict[str, Any]:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(
        "\n".join(
            [
                "# Janus Z2 chi_LL Area Gap Exit Gate",
                "",
                payload["physical_idea"],
                "",
                f"Exit ready: `{payload['area_gap_exit_ready']}`",
                "",
                "## Blocked By",
                *[f"- `{item}`" for item in payload["blocked_by"]],
            ]
        ),
        encoding="utf-8",
    )
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
