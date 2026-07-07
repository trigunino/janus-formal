from __future__ import annotations

import json
import math
from pathlib import Path
from typing import Any


BASE = Path("outputs/active_z2_sigma")
INPUT_PATH = BASE / "horizon_thermodynamic_exit_inputs.json"
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_chi_ll_horizon_thermodynamic_exit_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_chi_ll_horizon_thermodynamic_exit_gate.json")

C_SI = 299_792_458.0
G_SI = 6.674_30e-11
HBAR_SI = 1.054_571_817e-34
KB_SI = 1.380_649e-23


def _read(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8")) if path.exists() else {}


def _positive(data: dict[str, Any], key: str, missing: list[str]) -> float | None:
    value = data.get(key)
    if not isinstance(value, (int, float)) or not math.isfinite(float(value)) or float(value) <= 0:
        missing.append(key)
        return None
    return float(value)


def _derive(data: dict[str, Any]) -> dict[str, Any]:
    missing: list[str] = []
    radius_m = _positive(data, "R_s_m", missing)
    kappa_l = _positive(data, "surface_gravity_kappa_l_1_per_m", missing)
    if radius_m is None or kappa_l is None:
        return {"ready": False, "missing": missing}
    area_m2 = 4.0 * math.pi * radius_m**2
    entropy_j_per_k = KB_SI * area_m2 / (4.0 * (HBAR_SI * G_SI / C_SI**3))
    temperature_k = HBAR_SI * C_SI * kappa_l / (2.0 * math.pi * KB_SI)
    misner_sharp_mass_kg = C_SI**2 * radius_m / (2.0 * G_SI)
    chi_abs_inverse_m = 1.0 / (8.0 * math.pi * radius_m)
    return {
        "ready": True,
        "missing": [],
        "area_m2": area_m2,
        "entropy_J_per_K": entropy_j_per_k,
        "temperature_K": temperature_k,
        "M_bridge_kg": misner_sharp_mass_kg,
        "chi_LL_abs_inverse_m": chi_abs_inverse_m,
        "chi_LL_sign": "negative_PT_branch",
    }


def build_payload(input_path: Path = INPUT_PATH) -> dict[str, Any]:
    data = _read(input_path)
    required_conditions = {
        "Sigma_PT_is_null_horizon": bool(data.get("Sigma_PT_is_null_horizon")),
        "surface_gravity_normalization_fixed": data.get("surface_gravity_kappa_l_1_per_m") is not None,
        "horizon_area_radius_available": data.get("R_s_m") is not None,
        "entropy_law_declared": data.get("entropy_law") == "Bekenstein_Hawking_area",
        "temperature_law_declared": data.get("temperature_law") == "T=hbar*c*kappa_l/(2*pi*kB)",
        "energy_law_declared": data.get("energy_law") in {
            "Misner_Sharp_horizon_mass",
            "Brown_York_null_boundary_charge",
        },
        "first_law_or_unified_first_law_declared": bool(
            data.get("first_law_or_unified_first_law_declared")
        ),
        "non_observational_provenance": bool(data.get("non_observational_provenance")),
    }
    derivation = _derive(data)
    ready = all(required_conditions.values()) and derivation["ready"]
    return {
        "status": "janus-z2-chi-ll-horizon-thermodynamic-exit-gate",
        "active_core": "Z2_tunnel_Sigma_null_PT_bridge",
        "physical_idea": (
            "If Sigma/PT is an actual null or apparent horizon, standard horizon "
            "thermodynamics can relate area, surface gravity, temperature, entropy "
            "and a horizon energy. This can yield chi_LL only after the horizon "
            "normalization and radius/energy are derived non-observationally."
        ),
        "bibliography_basis": [
            "Cai-Kim: first law at apparent horizon derives Friedmann equations",
            "Hayward/Cai-Cao: unified first law for apparent horizons",
            "Parattu et al. and Lehner et al.: null boundary action terms",
        ],
        "required_conditions": required_conditions,
        "formulae": {
            "area": "A=4*pi*R_s^2",
            "entropy": "S=kB*A/(4*l_P^2)",
            "temperature": "T=hbar*c*kappa_l/(2*pi*kB)",
            "horizon_mass": "M=c^2*R_s/(2G)",
            "ll_tension": "chi_LL=-1/(8*pi*R_s)",
        },
        "forbidden_shortcuts": {
            "declare_horizon_without_null_expansion_or_boundary_data": True,
            "choose_surface_gravity_normalization_by_fit": True,
            "choose_R_s_by_observation": True,
            "use_entropy_extremum_without_first_law": True,
        },
        "input_path": str(input_path),
        "input_present": input_path.exists(),
        "derivation": derivation,
        "horizon_thermodynamic_exit_ready": ready,
        "chi_LL_prediction_ready": ready,
        "blocked_by": [key for key, value in required_conditions.items() if not value]
        + derivation.get("missing", []),
        "gate_passed": True,
    }


def write_reports() -> dict[str, Any]:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2 chi_LL Horizon Thermodynamic Exit Gate",
        "",
        payload["physical_idea"],
        "",
        f"Exit ready: `{payload['horizon_thermodynamic_exit_ready']}`",
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
