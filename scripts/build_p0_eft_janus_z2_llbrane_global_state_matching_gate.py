from __future__ import annotations

import json
import math
import sys
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z2_null_sigma_mass_charge_to_rs_gate import C_SI, G_SI


BASE = Path("outputs/active_z2_sigma")
CHI_PATH = BASE / "null_bridge_llbrane_tension_inputs.json"
MASS_PATH = BASE / "null_bridge_mass_charge_inputs.json"
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_llbrane_global_state_matching_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_llbrane_global_state_matching_gate.json")


def _read(path: Path) -> dict[str, Any] | None:
    if not path.exists():
        return None
    return json.loads(path.read_text(encoding="utf-8"))


def _chi_abs(payload: dict[str, Any]) -> float:
    value = float(payload["chi_LL_abs_inverse_m"])
    if value <= 0.0 or not math.isfinite(value):
        raise ValueError("chi_LL_abs_inverse_m must be positive finite")
    return value


def _mass(payload: dict[str, Any]) -> float:
    value = float(payload["M_bridge_kg"])
    if value <= 0.0 or not math.isfinite(value):
        raise ValueError("M_bridge_kg must be positive finite")
    return value


def chi_from_mass(m_bridge_kg: float) -> float:
    return C_SI * C_SI / (16.0 * math.pi * G_SI * m_bridge_kg)


def mass_from_chi(chi_abs_inverse_m: float) -> float:
    return C_SI * C_SI / (16.0 * math.pi * G_SI * chi_abs_inverse_m)


def build_payload(
    *,
    chi_path: Path = CHI_PATH,
    mass_path: Path = MASS_PATH,
    rel_tol: float = 1.0e-12,
) -> dict[str, Any]:
    chi_payload = _read(chi_path)
    mass_payload = _read(mass_path)
    chi_available = chi_payload is not None
    mass_available = mass_payload is not None
    validation_errors: list[str] = []
    match = False
    inferred = None

    try:
        if chi_payload is not None and mass_payload is not None:
            chi_value = _chi_abs(chi_payload)
            mass_value = _mass(mass_payload)
            inferred_mass = mass_from_chi(chi_value)
            inferred_chi = chi_from_mass(mass_value)
            match = math.isclose(inferred_mass, mass_value, rel_tol=rel_tol, abs_tol=0.0)
            inferred = {
                "chi_LL_abs_inverse_m": chi_value,
                "M_bridge_kg": mass_value,
                "M_from_chi_kg": inferred_mass,
                "chi_from_M_inverse_m": inferred_chi,
                "matching_relation": "M_bridge = c^2/(16*pi*G*abs(chi_LL))",
            }
        elif chi_payload is not None:
            chi_value = _chi_abs(chi_payload)
            inferred = {
                "chi_LL_abs_inverse_m": chi_value,
                "M_from_chi_kg": mass_from_chi(chi_value),
                "remaining_parameter": "chi_LL_abs_inverse_m",
            }
        elif mass_payload is not None:
            mass_value = _mass(mass_payload)
            inferred = {
                "M_bridge_kg": mass_value,
                "chi_from_M_inverse_m": chi_from_mass(mass_value),
                "remaining_parameter": "M_bridge_kg",
            }
    except Exception as exc:
        validation_errors.append(str(exc))

    reduces_two_parameters_to_one = chi_available or mass_available
    return {
        "status": "janus-z2-llbrane-global-state-matching-gate",
        "chi_input_exists": chi_available,
        "mass_input_exists": mass_available,
        "validation_errors": validation_errors,
        "matching_formulae": {
            "LL_brane_radius": "R_s = 1/(8*pi*abs(chi_LL))",
            "mass_radius": "R_s = 2*G*M_bridge/c^2",
            "combined": "M_bridge = c^2/(16*pi*G*abs(chi_LL))",
        },
        "inferred": inferred,
        "matching_passed": match,
        "reduces_two_parameters_to_one": reduces_two_parameters_to_one,
        "absolute_scale_selected": False,
        "extra_independent_state_law_required": True,
        "gate_passed": match,
        "next_required": []
        if match
        else [
            "derive_or_declare_one_clean_state_scale:chi_LL_or_M_bridge",
            "do_not_keep_chi_LL_and_M_bridge_independent",
            "derive_extra_independent_state_law_for_absolute_scale",
        ],
    }


def write_reports() -> dict[str, Any]:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2 LL-Brane / Global State Matching Gate",
        "",
        f"Chi input exists: `{payload['chi_input_exists']}`",
        f"Mass input exists: `{payload['mass_input_exists']}`",
        f"Matching passed: `{payload['matching_passed']}`",
        f"Reduces two parameters to one: `{payload['reduces_two_parameters_to_one']}`",
        f"Absolute scale selected: `{payload['absolute_scale_selected']}`",
        "",
        "## Formulae",
    ]
    lines.extend(f"- `{key}`: `{value}`" for key, value in payload["matching_formulae"].items())
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
