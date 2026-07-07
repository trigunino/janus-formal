from __future__ import annotations

import json
import math
import sys
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z2_null_sigma_mass_charge_to_rs_gate import (
    C_SI,
    G_SI,
)


BASE = Path("outputs/active_z2_sigma")
INPUT_PATH = BASE / "null_bridge_bulk_solution_rs_inputs.json"
OUTPUT_PATH = BASE / "null_bridge_global_mass_solution_inputs.json"
REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_null_sigma_bulk_rs_to_global_mass_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_null_sigma_bulk_rs_to_global_mass_gate.json"
)

FORBIDDEN_TOKENS = ("fit", "planck", "lcdm", "bao", "z4", "demo")


def _read(path: Path) -> dict[str, Any] | None:
    if not path.exists():
        return None
    return json.loads(path.read_text(encoding="utf-8"))


def _bad_provenance(value: Any) -> bool:
    text = str(value or "").strip().lower()
    return not text or any(token in text for token in FORBIDDEN_TOKENS)


def _valid_bulk_rs_payload(payload: dict[str, Any]) -> list[str]:
    errors: list[str] = []
    if payload.get("active_core") != "Z2_tunnel_Sigma":
        errors.append("active_core_must_be_Z2_tunnel_Sigma")
    if payload.get("branch") != "Z2_null_Sigma_PT_bridge":
        errors.append("branch_must_be_Z2_null_Sigma_PT_bridge")
    if payload.get("source") != "active_derived":
        errors.append("source_must_be_active_derived")
    if payload.get("bulk_solution_kind") != "Schwarzschild_PT_bridge":
        errors.append("bulk_solution_kind_must_be_Schwarzschild_PT_bridge")

    rs = payload.get("R_s_m")
    if not isinstance(rs, (int, float)) or not math.isfinite(float(rs)) or rs <= 0:
        errors.append("R_s_m_must_be_positive_finite")

    if payload.get("PT_energy_sign_reversal_proved") is not True:
        errors.append("PT_energy_sign_reversal_must_be_proved")
    if payload.get("R_Sigma_equals_R_s_proved") is not True:
        errors.append("R_Sigma_equals_R_s_must_be_proved")
    if _bad_provenance(payload.get("R_s_provenance")):
        errors.append("R_s_provenance_missing_or_forbidden")

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
    rs_payload = _read(input_path)
    errors = [] if rs_payload is None else _valid_bulk_rs_payload(rs_payload)
    ready = rs_payload is not None and not errors
    global_mass_payload = None

    if ready:
        rs = float(rs_payload["R_s_m"])
        mass = (C_SI * C_SI * rs) / (2.0 * G_SI)
        global_mass_payload = {
            "active_core": "Z2_tunnel_Sigma",
            "branch": "Z2_null_Sigma_PT_bridge",
            "source": "active_derived",
            "M_plus_kg": mass,
            "M_minus_kg": -mass,
            "PT_energy_sign_reversal_proved": True,
            "bimetric_global_solution_proved": True,
            "M_bridge_role": "bulk_solution_or_Noether_state_label",
            "M_bridge_provenance": (
                f"bulk_rs_solution:{rs_payload['R_s_provenance']}"
            ),
            "observational_fit_used": False,
            "compressed_planck_lcdm_background_used": False,
            "archived_z4_reuse_used": False,
        }
        if write_output:
            output_path.parent.mkdir(parents=True, exist_ok=True)
            output_path.write_text(
                json.dumps(global_mass_payload, indent=2), encoding="utf-8"
            )

    return {
        "status": "janus-z2-null-sigma-bulk-rs-to-global-mass-gate",
        "active_core": "Z2_tunnel_Sigma",
        "branch": "Z2_null_Sigma_PT_bridge",
        "input_path": str(input_path),
        "output_path": str(output_path),
        "input_exists": rs_payload is not None,
        "formula": "M_bridge = c^2 * R_s / (2*G)",
        "validation_errors": errors,
        "bulk_Rs_solution_available": ready,
        "global_mass_solution_available": ready,
        "global_mass_payload": global_mass_payload,
        "gate_passed": ready,
        "next_required": []
        if ready
        else [
            "derive_absolute_R_s_m_from_active_Schwarzschild_PT_bulk_solution",
            "prove_R_Sigma_equals_R_s_on_active_bridge",
            "do_not_choose_R_s_by_observational_fit",
        ],
    }


def write_reports() -> dict[str, Any]:
    payload = build_payload(write_output=True)
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2 Null Sigma Bulk R_s To Global Mass Gate",
        "",
        f"Bulk R_s solution available: `{payload['bulk_Rs_solution_available']}`",
        f"Global mass solution available: `{payload['global_mass_solution_available']}`",
        f"Formula: `{payload['formula']}`",
        "",
        "## Next Required",
    ]
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
