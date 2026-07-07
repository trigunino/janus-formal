from __future__ import annotations

import json
import math
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_chi_ll_casimir_topological_exit_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_chi_ll_casimir_topological_exit_gate.json")

C_SI = 299_792_458.0
G_SI = 6.674_30e-11


def derive_from_inputs(data: dict) -> dict:
    coeff = data.get("casimir_coefficient_C")
    radius_m = data.get("R_s_m")
    if coeff is None or radius_m is None:
        return {"ready": False, "missing": ["casimir_coefficient_C", "R_s_m"]}
    coeff = float(coeff)
    radius_m = float(radius_m)
    if radius_m <= 0:
        return {"ready": False, "missing": ["positive_R_s_m"]}
    energy_density_j_m3 = coeff / radius_m**4
    mass_density_kg_m3 = energy_density_j_m3 / C_SI**2
    m_bridge_kg = C_SI**2 * radius_m / (2 * G_SI)
    chi_abs_inverse_m = 1.0 / (8.0 * math.pi * radius_m)
    return {
        "ready": True,
        "missing": [],
        "rho_casimir_J_m3": energy_density_j_m3,
        "rho_casimir_kg_m3": mass_density_kg_m3,
        "M_bridge_kg": m_bridge_kg,
        "chi_LL_abs_inverse_m": chi_abs_inverse_m,
        "chi_LL_sign": "negative_PT_branch",
    }


def build_payload(input_path: Path = Path("outputs/active_z2_sigma/casimir_topological_exit_inputs.json")) -> dict:
    data = json.loads(input_path.read_text(encoding="utf-8")) if input_path.exists() else {}
    required_conditions = {
        "compact_throat_topology_declared": bool(data.get("compact_throat_topology_declared")),
        "quantum_field_content_declared": bool(data.get("quantum_field_content_declared")),
        "boundary_conditions_declared": bool(data.get("boundary_conditions_declared")),
        "renormalization_reference_declared": bool(data.get("renormalization_reference_declared")),
        "casimir_coefficient_C_derived": data.get("casimir_coefficient_C") is not None,
        "absolute_radius_or_stationarity_equation_available": (
            data.get("R_s_m") is not None or bool(data.get("stationarity_equation_declared"))
        ),
    }
    derivation = derive_from_inputs(data)
    all_conditions = all(required_conditions.values())
    prediction_ready = all_conditions and derivation["ready"]
    return {
        "status": "janus-z2-chi-ll-casimir-topological-exit-gate",
        "active_core": "Z2_tunnel_Sigma_null_PT_bridge",
        "physical_idea": (
            "A compact throat can carry renormalized vacuum energy scaling like "
            "rho_Casimir = C/R_s^4. This can affect the bridge scale only if "
            "field content, boundary conditions, reference subtraction and an "
            "absolute radius or stationarity law are derived."
        ),
        "bibliography_basis": [
            "Thermal Casimir effect in closed Friedmann universe",
            "Topological Casimir effect in compact electrodynamics",
            "Casimir energy in compact/cosmic topology models",
        ],
        "required_conditions": required_conditions,
        "forbidden_shortcuts": {
            "choose_C_to_fit_H0": True,
            "choose_R_s_to_fit_observations": True,
            "use_Casimir_without_field_content": True,
            "use_Casimir_without_boundary_conditions": True,
            "ignore_renormalization_reference": True,
        },
        "formulae": {
            "rho_casimir": "rho_C = C/R_s^4",
            "bridge_mass": "M_bridge = c^2 R_s/(2G)",
            "ll_tension": "chi_LL = -1/(8*pi*R_s)",
        },
        "active_input_path": str(input_path),
        "input_present": input_path.exists(),
        "derivation": derivation,
        "casimir_exit_prediction_ready": prediction_ready,
        "chi_LL_prediction_ready": prediction_ready,
        "blocked_by": [key for key, value in required_conditions.items() if not value]
        + derivation.get("missing", []),
        "gate_passed": True,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2 chi_LL Casimir Topological Exit Gate",
        "",
        payload["physical_idea"],
        "",
        f"Prediction ready: `{payload['casimir_exit_prediction_ready']}`",
        f"Input present: `{payload['input_present']}`",
        "",
        "## Required Conditions",
    ]
    lines.extend(f"- `{k}`: `{v}`" for k, v in payload["required_conditions"].items())
    lines.extend(["", "## Blocked By"])
    lines.extend(f"- `{item}`" for item in payload["blocked_by"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
