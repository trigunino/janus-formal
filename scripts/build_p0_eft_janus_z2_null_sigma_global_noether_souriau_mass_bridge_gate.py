from __future__ import annotations

import json
import math
from pathlib import Path
from typing import Any


BASE = Path("outputs/active_z2_sigma")
INPUT_PATH = BASE / "null_bridge_global_mass_solution_inputs.json"
OUTPUT_PATH = BASE / "null_bridge_mass_charge_inputs.json"
REPORT_PATH = Path(
    "outputs/reports/"
    "p0_eft_janus_z2_null_sigma_global_noether_souriau_mass_bridge_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/"
    "p0_eft_janus_z2_null_sigma_global_noether_souriau_mass_bridge_gate.json"
)

FORBIDDEN_TOKENS = ("fit", "planck", "lcdm", "bao", "z4", "demo")


def _read(path: Path) -> dict[str, Any] | None:
    if not path.exists():
        return None
    return json.loads(path.read_text(encoding="utf-8"))


def _bad_text(value: Any) -> bool:
    text = str(value or "").strip().lower()
    return not text or any(token in text for token in FORBIDDEN_TOKENS)


def _valid_global_mass_payload(payload: dict[str, Any]) -> list[str]:
    errors: list[str] = []
    if payload.get("active_core") != "Z2_tunnel_Sigma":
        errors.append("active_core_must_be_Z2_tunnel_Sigma")
    if payload.get("branch") != "Z2_null_Sigma_PT_bridge":
        errors.append("branch_must_be_Z2_null_Sigma_PT_bridge")
    if payload.get("source") != "active_derived":
        errors.append("source_must_be_active_derived")

    plus = payload.get("M_plus_kg")
    minus = payload.get("M_minus_kg")
    if not isinstance(plus, (int, float)) or not math.isfinite(float(plus)):
        errors.append("M_plus_kg_must_be_finite")
    if not isinstance(minus, (int, float)) or not math.isfinite(float(minus)):
        errors.append("M_minus_kg_must_be_finite")
    if not errors:
        plus_f = float(plus)
        minus_f = float(minus)
        if plus_f <= 0:
            errors.append("M_plus_kg_must_be_positive")
        if not math.isclose(minus_f, -plus_f, rel_tol=1e-12, abs_tol=1e-30):
            errors.append("Souriau_PT_mass_pair_must_satisfy_M_minus_equals_minus_M_plus")

    if payload.get("PT_energy_sign_reversal_proved") is not True:
        errors.append("PT_energy_sign_reversal_must_be_proved")
    if payload.get("bimetric_global_solution_proved") is not True:
        errors.append("bimetric_global_solution_must_be_proved")
    if payload.get("M_bridge_role") != "bulk_solution_or_Noether_state_label":
        errors.append("M_bridge_role_must_be_bulk_solution_or_Noether_state_label")
    if _bad_text(payload.get("M_bridge_provenance")):
        errors.append("M_bridge_provenance_missing_or_forbidden")

    for key in [
        "observational_fit_used",
        "compressed_planck_lcdm_background_used",
        "archived_z4_reuse_used",
    ]:
        if payload.get(key) is True:
            errors.append(f"forbidden_flag:{key}")
    return errors


def build_payload(
    *,
    input_path: Path = INPUT_PATH,
    output_path: Path = OUTPUT_PATH,
    write_output: bool = False,
) -> dict[str, Any]:
    global_payload = _read(input_path)
    errors = [] if global_payload is None else _valid_global_mass_payload(global_payload)
    ready = global_payload is not None and not errors
    mass_payload = None

    if ready:
        mass = float(global_payload["M_plus_kg"])
        mass_payload = {
            "active_core": "Z2_tunnel_Sigma",
            "branch": "Z2_null_Sigma_PT_bridge",
            "source": "active_derived",
            "M_bridge_kg": mass,
            "M_bridge_provenance": (
                "global_noether_souriau:"
                f"{global_payload['M_bridge_provenance']}"
            ),
            "mass_sign_policy": "PT_abs_mass_for_radius",
            "observational_fit_used": False,
            "compressed_planck_lcdm_background_used": False,
            "archived_z4_reuse_used": False,
        }
        if write_output:
            output_path.parent.mkdir(parents=True, exist_ok=True)
            output_path.write_text(json.dumps(mass_payload, indent=2), encoding="utf-8")

    return {
        "status": "janus-z2-null-sigma-global-noether-souriau-mass-bridge-gate",
        "active_core": "Z2_tunnel_Sigma",
        "branch": "Z2_null_Sigma_PT_bridge",
        "input_path": str(input_path),
        "output_path": str(output_path),
        "input_exists": global_payload is not None,
        "souriau_PT_sign_law": {
            "energy_mass_sign_reversal": True,
            "pairing_constraint": "M_minus = -M_plus",
            "bridge_radius_uses_abs_mass": True,
        },
        "bimetric_noether_result": {
            "global_charge_kind": "Hamiltonian/Noether mass label",
            "sign_pairing_fixed": True,
            "absolute_magnitude_fixed_by_symmetry": False,
            "absolute_magnitude_requires": [
                "active_bimetric_bulk_solution_mass_parameter",
                "or_global_Noether_state_charge",
                "or_state_selection_law_for_bridge_mass",
            ],
        },
        "validation_errors": errors,
        "global_mass_solution_available": ready,
        "M_bridge_available": ready,
        "mass_payload": mass_payload,
        "gate_passed": ready,
        "next_required": []
        if ready
        else [
            "derive_M_plus_kg_from_active_bimetric_bulk_solution_or_Noether_state",
            "prove_PT_pairing_M_minus_equals_minus_M_plus",
            "do_not_choose_M_bridge_by_observational_fit",
        ],
    }


def write_reports() -> dict[str, Any]:
    payload = build_payload(write_output=True)
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2 Null Sigma Global Noether/Souriau Mass Bridge Gate",
        "",
        f"Global mass solution available: `{payload['global_mass_solution_available']}`",
        f"M_bridge available: `{payload['M_bridge_available']}`",
        "",
        "## Result",
        "- Souriau/PT fixes the sign pairing `M_minus = -M_plus`.",
        "- The absolute magnitude is not fixed by symmetry alone.",
        "",
        "## Next Required",
    ]
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
