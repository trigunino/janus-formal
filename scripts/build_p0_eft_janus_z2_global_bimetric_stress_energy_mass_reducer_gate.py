from __future__ import annotations

import json
import math
from pathlib import Path
from typing import Any


BASE = Path("outputs/active_z2_sigma")
INPUT_PATH = BASE / "global_bimetric_stress_energy_state_inputs.json"
OUTPUT_PATH = BASE / "null_bridge_global_mass_solution_inputs.json"
REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_global_bimetric_stress_energy_mass_reducer_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_global_bimetric_stress_energy_mass_reducer_gate.json"
)
FORBIDDEN_TOKENS = ("fit", "planck", "lcdm", "bao", "z4", "demo")


def _read(path: Path) -> dict[str, Any] | None:
    if not path.exists():
        return None
    return json.loads(path.read_text(encoding="utf-8"))


def _bad_provenance(value: Any) -> bool:
    text = str(value or "").strip().lower()
    return not text or any(token in text for token in FORBIDDEN_TOKENS)


def _positive_finite(value: Any) -> bool:
    return isinstance(value, (int, float)) and math.isfinite(float(value)) and value > 0


def _valid_input(payload: dict[str, Any]) -> list[str]:
    errors: list[str] = []
    if payload.get("active_core") != "Z2_tunnel_Sigma":
        errors.append("active_core_must_be_Z2_tunnel_Sigma")
    if payload.get("source") != "active_derived":
        errors.append("source_must_be_active_derived")
    if payload.get("stress_energy_state_proved") is not True:
        errors.append("stress_energy_state_must_be_proved")
    if payload.get("PT_energy_sign_reversal_proved") is not True:
        errors.append("PT_energy_sign_reversal_must_be_proved")
    if _bad_provenance(payload.get("state_provenance")):
        errors.append("state_provenance_missing_or_forbidden")

    has_mass = _positive_finite(payload.get("M_plus_kg"))
    has_density_volume = _positive_finite(payload.get("rho_plus_kg_m3")) and _positive_finite(
        payload.get("V_plus_m3")
    )
    if not (has_mass or has_density_volume):
        errors.append("need_M_plus_kg_or_rho_plus_kg_m3_times_V_plus_m3")

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
    state = _read(input_path)
    errors = [] if state is None else _valid_input(state)
    ready = state is not None and not errors
    global_mass_payload = None

    if ready:
        if _positive_finite(state.get("M_plus_kg")):
            mass = float(state["M_plus_kg"])
            reduction = "direct_active_M_plus_kg"
        else:
            mass = float(state["rho_plus_kg_m3"]) * float(state["V_plus_m3"])
            reduction = "rho_plus_kg_m3_times_V_plus_m3"
        global_mass_payload = {
            "active_core": "Z2_tunnel_Sigma",
            "branch": "Z2_null_Sigma_PT_bridge",
            "source": "active_derived",
            "M_plus_kg": mass,
            "M_minus_kg": -mass,
            "PT_energy_sign_reversal_proved": True,
            "bimetric_global_solution_proved": True,
            "M_bridge_role": "bulk_solution_or_Noether_state_label",
            "M_bridge_provenance": f"global_stress_energy:{state['state_provenance']}",
            "mass_reduction": reduction,
            "observational_fit_used": False,
            "compressed_planck_lcdm_background_used": False,
            "archived_z4_reuse_used": False,
        }
        if write_output:
            output_path.parent.mkdir(parents=True, exist_ok=True)
            output_path.write_text(json.dumps(global_mass_payload, indent=2), encoding="utf-8")

    return {
        "status": "janus-z2-global-bimetric-stress-energy-mass-reducer-gate",
        "input_path": str(input_path),
        "output_path": str(output_path),
        "input_exists": state is not None,
        "validation_errors": errors,
        "global_stress_energy_mass_available": ready,
        "global_mass_payload": global_mass_payload,
        "gate_passed": ready,
        "next_required": []
        if ready
        else [
            "derive_global_bimetric_stress_energy_state",
            "provide_M_plus_kg_or_rho_plus_kg_m3_times_V_plus_m3",
            "prove_PT_energy_sign_reversal",
        ],
    }


def write_reports() -> dict[str, Any]:
    payload = build_payload(write_output=True)
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2 Global Bimetric Stress-Energy Mass Reducer Gate",
        "",
        f"Input exists: `{payload['input_exists']}`",
        f"Global stress-energy mass available: `{payload['global_stress_energy_mass_available']}`",
        "",
        "## Next Required",
    ]
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
