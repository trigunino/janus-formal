from __future__ import annotations

import json
import math
from pathlib import Path
from typing import Any


BASE = Path("outputs/active_z2_sigma")
INPUT_PATH = BASE / "null_bridge_mass_charge_inputs.json"
OUTPUT_PATH = BASE / "null_bridge_rs_scale_inputs.json"
REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_null_sigma_mass_charge_to_rs_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_null_sigma_mass_charge_to_rs_gate.json"
)

G_SI = 6.67430e-11
C_SI = 299_792_458.0
FORBIDDEN_TOKENS = ("fit", "planck", "lcdm", "bao", "z4", "demo")


def _read(path: Path) -> dict[str, Any] | None:
    if not path.exists():
        return None
    return json.loads(path.read_text(encoding="utf-8"))


def _valid_mass_payload(payload: dict[str, Any]) -> list[str]:
    errors: list[str] = []
    if payload.get("active_core") != "Z2_tunnel_Sigma":
        errors.append("active_core_must_be_Z2_tunnel_Sigma")
    if payload.get("branch") != "Z2_null_Sigma_PT_bridge":
        errors.append("branch_must_be_Z2_null_Sigma_PT_bridge")
    if payload.get("source") != "active_derived":
        errors.append("source_must_be_active_derived")
    mass = payload.get("M_bridge_kg")
    if not isinstance(mass, (int, float)) or not math.isfinite(float(mass)) or mass <= 0:
        errors.append("M_bridge_kg_must_be_positive_finite")
    provenance = str(payload.get("M_bridge_provenance", "")).strip()
    if not provenance:
        errors.append("M_bridge_provenance_must_be_nonempty")
    if any(token in provenance.lower() for token in FORBIDDEN_TOKENS):
        errors.append("M_bridge_provenance_contains_forbidden_token")
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
    mass_payload = _read(input_path)
    errors = [] if mass_payload is None else _valid_mass_payload(mass_payload)
    ready = mass_payload is not None and not errors
    rs_payload = None
    if ready:
        mass = float(mass_payload["M_bridge_kg"])
        rs = 2.0 * G_SI * mass / (C_SI * C_SI)
        rs_payload = {
            "active_core": "Z2_tunnel_Sigma",
            "branch": "Z2_null_Sigma_PT_bridge",
            "source": "active_derived_mass_charge",
            "M_bridge_kg": mass,
            "M_bridge_provenance": mass_payload["M_bridge_provenance"],
            "R_s_m": rs,
            "R_Sigma_abs_m": rs,
            "formula": "R_s = 2*G*M_bridge/c^2",
            "observational_fit_used": False,
            "compressed_planck_lcdm_background_used": False,
            "archived_z4_reuse_used": False,
            "absolute_Rs_selected": True,
        }
        if write_output:
            output_path.parent.mkdir(parents=True, exist_ok=True)
            output_path.write_text(json.dumps(rs_payload, indent=2), encoding="utf-8")
    return {
        "status": "janus-z2-null-sigma-mass-charge-to-rs-gate",
        "active_core": "Z2_tunnel_Sigma",
        "branch": "Z2_null_Sigma_PT_bridge",
        "input_path": str(input_path),
        "output_path": str(output_path),
        "input_exists": mass_payload is not None,
        "validation_errors": errors,
        "mass_charge_available": ready,
        "absolute_Rs_selected": ready,
        "rs_payload": rs_payload,
        "gate_passed": ready,
        "next_required": []
        if ready
        else [
            "derive_active_null_bridge_mass_charge_M_bridge_kg",
            "prove_M_bridge_from_Janus_state_or_bulk_solution",
            "do_not_choose_M_bridge_by_observational_fit",
        ],
    }


def write_reports() -> dict[str, Any]:
    payload = build_payload(write_output=True)
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2 Null Sigma Mass Charge To R_s Gate",
        "",
        f"Mass charge available: `{payload['mass_charge_available']}`",
        f"Absolute R_s selected: `{payload['absolute_Rs_selected']}`",
        "",
        "## Next Required",
    ]
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
