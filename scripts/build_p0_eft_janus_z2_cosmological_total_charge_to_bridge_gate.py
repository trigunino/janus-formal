from __future__ import annotations

import json
import math
import sys
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z2_global_bimetric_stress_energy_mass_reducer_gate import (
    build_payload as build_global_mass_reducer,
)
from scripts.build_p0_eft_janus_z2_null_sigma_global_noether_souriau_mass_bridge_gate import (
    build_payload as build_bridge_reducer,
)


BASE = Path("outputs/active_z2_sigma")
PROJECTION_PATH = BASE / "cosmological_charge_sigma_projection_inputs.json"
GLOBAL_MASS_PATH = BASE / "global_bimetric_stress_energy_state_inputs.json"
GLOBAL_SOLUTION_PATH = BASE / "null_bridge_global_mass_solution_inputs.json"
MASS_CHARGE_PATH = BASE / "null_bridge_mass_charge_inputs.json"
REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_cosmological_total_charge_to_bridge_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_cosmological_total_charge_to_bridge_gate.json"
)
FORBIDDEN_TOKENS = ("fit", "planck", "lcdm", "bao", "z4", "demo")


def _read(path: Path) -> dict[str, Any] | None:
    if not path.exists():
        return None
    return json.loads(path.read_text(encoding="utf-8"))


def _bad_text(value: Any) -> bool:
    text = str(value or "").strip().lower()
    return not text or any(token in text for token in FORBIDDEN_TOKENS)


def _valid_projection(payload: dict[str, Any]) -> list[str]:
    errors: list[str] = []
    if payload.get("active_core") != "Z2_tunnel_Sigma":
        errors.append("active_core_must_be_Z2_tunnel_Sigma")
    if payload.get("branch") != "Z2_null_Sigma_PT_bridge":
        errors.append("branch_must_be_Z2_null_Sigma_PT_bridge")
    if payload.get("source") != "active_derived":
        errors.append("source_must_be_active_derived")
    if payload.get("visible_charge_conserved_to_Sigma") is not True:
        errors.append("visible_charge_conservation_to_Sigma_must_be_proved")
    if payload.get("Sigma_projection_complete") is not True:
        errors.append("Sigma_projection_complete_must_be_proved")
    if payload.get("Q_Sigma_equals_M_bridge_c2") is not True:
        errors.append("Q_Sigma_equals_M_bridge_c2_must_be_proved")
    factor = payload.get("projection_factor_to_bridge")
    if not isinstance(factor, (int, float)) or not math.isfinite(float(factor)):
        errors.append("projection_factor_to_bridge_must_be_finite")
    elif float(factor) <= 0.0:
        errors.append("projection_factor_to_bridge_must_be_positive")
    if _bad_text(payload.get("projection_provenance")):
        errors.append("projection_provenance_missing_or_forbidden")
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
    projection_path: Path = PROJECTION_PATH,
    global_mass_path: Path = GLOBAL_MASS_PATH,
    global_solution_path: Path = GLOBAL_SOLUTION_PATH,
    mass_charge_path: Path = MASS_CHARGE_PATH,
    write_output: bool = False,
) -> dict[str, Any]:
    projection = _read(projection_path)
    projection_errors = (
        ["missing_cosmological_charge_sigma_projection_inputs"]
        if projection is None
        else _valid_projection(projection)
    )
    projection_ready = projection is not None and not projection_errors
    global_mass = build_global_mass_reducer(
        input_path=global_mass_path,
        output_path=global_solution_path,
        write_output=False,
    )
    bridge = None
    bridge_payload = None

    if projection_ready and global_mass["gate_passed"]:
        factor = float(projection["projection_factor_to_bridge"])
        base_solution = dict(global_mass["global_mass_payload"])
        base_solution["M_plus_kg"] = float(base_solution["M_plus_kg"]) * factor
        base_solution["M_minus_kg"] = -base_solution["M_plus_kg"]
        base_solution["M_bridge_provenance"] = (
            f"cosmological_total_charge_projection:{projection['projection_provenance']}"
        )
        if write_output:
            global_solution_path.parent.mkdir(parents=True, exist_ok=True)
            global_solution_path.write_text(
                json.dumps(base_solution, indent=2),
                encoding="utf-8",
            )
        temp_path = global_solution_path
        if write_output:
            bridge = build_bridge_reducer(
                input_path=temp_path,
                output_path=mass_charge_path,
                write_output=True,
            )
        else:
            # Avoid writing in dry mode; validate same schema directly.
            scratch = BASE / "_cosmological_total_charge_to_bridge_dry_run.json"
            scratch.parent.mkdir(parents=True, exist_ok=True)
            scratch.write_text(json.dumps(base_solution, indent=2), encoding="utf-8")
            try:
                bridge = build_bridge_reducer(
                    input_path=scratch,
                    output_path=mass_charge_path,
                    write_output=False,
                )
            finally:
                try:
                    scratch.unlink()
                except OSError:
                    pass
        bridge_payload = bridge["mass_payload"] if bridge else None

    gate_passed = bool(projection_ready and global_mass["gate_passed"] and bridge and bridge["gate_passed"])
    return {
        "status": "janus-z2-cosmological-total-charge-to-bridge-gate",
        "active_core": "Z2_tunnel_Sigma",
        "branch": "Z2_null_Sigma_PT_bridge",
        "physical_question": (
            "Does the conserved visible-sector total charge project onto Sigma/PT "
            "as the bridge mass M_bridge?"
        ),
        "projection_input_exists": projection is not None,
        "projection_errors": projection_errors,
        "projection_ready": projection_ready,
        "global_mass_ready": global_mass["gate_passed"],
        "bridge_mass_ready": bool(bridge and bridge["gate_passed"]),
        "bridge_payload": bridge_payload,
        "gate_passed": gate_passed,
        "closed_if_passed": [
            "visible_charge_conserved_to_Sigma",
            "active_global_mass_or_density_volume_available",
            "Sigma_projection_complete",
            "Q_Sigma_equals_M_bridge_c2",
        ],
        "next_required": []
        if gate_passed
        else [
            "derive_projected_visible_total_charge_or_global_mass_state",
            "derive_active_spatial_volume_or_absolute_mass_normalization",
            "prove_Sigma_PT_projection_factor_to_bridge",
            "prove_Q_Sigma_equals_M_bridge_c2",
        ],
        "interpretation": (
            "The user's intuition is encoded as a strict test. It can close only "
            "if the visible total charge is conserved to Sigma, the active global "
            "mass is available, and the Sigma/PT projection is proved."
        ),
    }


def write_reports() -> dict[str, Any]:
    payload = build_payload(write_output=True)
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2 Cosmological Total Charge To Bridge Gate",
        "",
        payload["interpretation"],
        "",
        f"Projection ready: `{payload['projection_ready']}`",
        f"Global mass ready: `{payload['global_mass_ready']}`",
        f"Bridge mass ready: `{payload['bridge_mass_ready']}`",
        f"Gate passed: `{payload['gate_passed']}`",
        "",
        "## Next Required",
    ]
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
