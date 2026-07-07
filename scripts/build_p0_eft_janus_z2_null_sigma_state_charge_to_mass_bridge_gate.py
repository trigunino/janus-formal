from __future__ import annotations

import json
import math
from pathlib import Path
from typing import Any


BASE = Path("outputs/active_z2_sigma")
INPUT_PATH = BASE / "null_bridge_state_mass_inputs.json"
OUTPUT_PATH = BASE / "null_bridge_mass_charge_inputs.json"
REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_null_sigma_state_charge_to_mass_bridge_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_null_sigma_state_charge_to_mass_bridge_gate.json"
)

FORBIDDEN_TOKENS = ("fit", "planck", "lcdm", "bao", "z4", "demo")


def _read(path: Path) -> dict[str, Any] | None:
    if not path.exists():
        return None
    return json.loads(path.read_text(encoding="utf-8"))


def _bad_provenance(value: Any) -> bool:
    text = str(value or "").strip().lower()
    return not text or any(token in text for token in FORBIDDEN_TOKENS)


def _valid_state_mass_payload(payload: dict[str, Any]) -> list[str]:
    errors: list[str] = []
    if payload.get("active_core") != "Z2_tunnel_Sigma":
        errors.append("active_core_must_be_Z2_tunnel_Sigma")
    if payload.get("branch") != "Z2_null_Sigma_PT_bridge":
        errors.append("branch_must_be_Z2_null_Sigma_PT_bridge")
    if payload.get("source") != "active_derived":
        errors.append("source_must_be_active_derived")

    occupation = payload.get("N_occ_Z2Sigma")
    if (
        not isinstance(occupation, (int, float))
        or not math.isfinite(float(occupation))
        or occupation <= 0
    ):
        errors.append("N_occ_Z2Sigma_must_be_positive_finite")

    mass_unit = payload.get("m_bridge_unit_kg")
    if (
        not isinstance(mass_unit, (int, float))
        or not math.isfinite(float(mass_unit))
        or mass_unit <= 0
    ):
        errors.append("m_bridge_unit_kg_must_be_positive_finite")

    if payload.get("mass_sign_policy") != "PT_abs_mass_for_radius":
        errors.append("mass_sign_policy_must_be_PT_abs_mass_for_radius")
    if _bad_provenance(payload.get("N_occ_provenance")):
        errors.append("N_occ_provenance_missing_or_forbidden")
    if _bad_provenance(payload.get("m_bridge_unit_provenance")):
        errors.append("m_bridge_unit_provenance_missing_or_forbidden")

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
    state_payload = _read(input_path)
    errors = [] if state_payload is None else _valid_state_mass_payload(state_payload)
    ready = state_payload is not None and not errors
    mass_payload = None

    if ready:
        occupation = float(state_payload["N_occ_Z2Sigma"])
        mass_unit = float(state_payload["m_bridge_unit_kg"])
        mass = occupation * mass_unit
        mass_payload = {
            "active_core": "Z2_tunnel_Sigma",
            "branch": "Z2_null_Sigma_PT_bridge",
            "source": "active_derived",
            "M_bridge_kg": mass,
            "M_bridge_provenance": (
                "state_charge_mass:"
                f"N_occ({state_payload['N_occ_provenance']})*"
                f"m_unit({state_payload['m_bridge_unit_provenance']})"
            ),
            "mass_sign_policy": state_payload["mass_sign_policy"],
            "observational_fit_used": False,
            "compressed_planck_lcdm_background_used": False,
            "archived_z4_reuse_used": False,
        }
        if write_output:
            output_path.parent.mkdir(parents=True, exist_ok=True)
            output_path.write_text(json.dumps(mass_payload, indent=2), encoding="utf-8")

    return {
        "status": "janus-z2-null-sigma-state-charge-to-mass-bridge-gate",
        "active_core": "Z2_tunnel_Sigma",
        "branch": "Z2_null_Sigma_PT_bridge",
        "input_path": str(input_path),
        "output_path": str(output_path),
        "input_exists": state_payload is not None,
        "validation_errors": errors,
        "state_charge_mass_available": ready,
        "M_bridge_available": ready,
        "mass_payload": mass_payload,
        "gate_passed": ready,
        "next_required": []
        if ready
        else [
            "derive_N_occ_Z2Sigma_from_boundary_state_or_superselection",
            "derive_m_bridge_unit_kg_from_active_matter_or_bridge_state",
            "do_not_choose_M_bridge_by_observational_fit",
        ],
    }


def write_reports() -> dict[str, Any]:
    payload = build_payload(write_output=True)
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2 Null Sigma State Charge To Mass Bridge Gate",
        "",
        f"State charge mass available: `{payload['state_charge_mass_available']}`",
        f"M_bridge available: `{payload['M_bridge_available']}`",
        "",
        "## Next Required",
    ]
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
