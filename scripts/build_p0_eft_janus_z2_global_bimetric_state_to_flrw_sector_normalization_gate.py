from __future__ import annotations

import json
import math
from pathlib import Path
from typing import Any


BASE = Path("outputs/active_z2_sigma")
INPUT_PATH = BASE / "global_bimetric_stress_energy_state_inputs.json"
OUTPUT_PATH = BASE / "published_bimetric_flrw_sector_normalization_inputs.json"
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_global_bimetric_state_to_flrw_sector_normalization_gate.json")
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_global_bimetric_state_to_flrw_sector_normalization_gate.md")
FORBIDDEN = ("fit", "planck", "lcdm", "bao", "z4", "demo")


def _read(path: Path) -> dict[str, Any] | None:
    return json.loads(path.read_text(encoding="utf-8")) if path.exists() else None


def _bad_provenance(text: Any) -> bool:
    lower = str(text or "").lower()
    return not lower.strip() or any(token in lower for token in FORBIDDEN)


def _positive(value: Any) -> bool:
    return isinstance(value, (int, float)) and math.isfinite(float(value)) and float(value) > 0.0


def _negative(value: Any) -> bool:
    return isinstance(value, (int, float)) and math.isfinite(float(value)) and float(value) < 0.0


def _validate(state: dict[str, Any]) -> list[str]:
    errors: list[str] = []
    if state.get("active_core") != "Z2_tunnel_Sigma":
        errors.append("active_core_must_be_Z2_tunnel_Sigma")
    if state.get("source") != "active_derived":
        errors.append("source_must_be_active_derived")
    if state.get("stress_energy_state_proved") is not True:
        errors.append("stress_energy_state_must_be_proved")
    if state.get("PT_energy_sign_reversal_proved") is not True:
        errors.append("PT_energy_sign_reversal_must_be_proved")
    if _bad_provenance(state.get("state_provenance")):
        errors.append("state_provenance_missing_or_forbidden")
    if not _positive(state.get("rho_plus_kg_m3")):
        errors.append("rho_plus_kg_m3_missing_or_nonpositive")
    if "rho_minus_kg_m3" in state and not _negative(state["rho_minus_kg_m3"]):
        errors.append("rho_minus_kg_m3_must_be_negative_if_present")
    for key in [
        "observational_fit_used",
        "compressed_planck_lcdm_background_used",
        "archived_z4_reuse_used",
    ]:
        if state.get(key) is True:
            errors.append(f"forbidden_flag:{key}")
    return errors


def build_payload(
    *,
    input_path: Path = INPUT_PATH,
    output_path: Path = OUTPUT_PATH,
    write_output: bool = False,
) -> dict[str, Any]:
    state = _read(input_path)
    errors = ["missing_global_bimetric_stress_energy_state_inputs"] if state is None else _validate(state)
    normalized = None
    if state is not None and not errors:
        rho_plus = float(state["rho_plus_kg_m3"])
        rho_minus = float(state.get("rho_minus_kg_m3", -rho_plus))
        normalized = {
            "active_core": "Z2_tunnel_Sigma",
            "source": "active_derived",
            "rho_plus0_kg_m3": rho_plus,
            "rho_minus0_kg_m3": rho_minus,
            "p_plus0_pa": float(state.get("p_plus0_pa", 0.0)),
            "p_minus0_pa": float(state.get("p_minus0_pa", 0.0)),
            "equation_of_state": state.get("equation_of_state", "dust"),
            "PT_energy_sign_reversal_proved": True,
            "normalization_provenance": f"global_bimetric_state:{state['state_provenance']}",
            "observational_fit_used": False,
            "compressed_planck_lcdm_background_used": False,
            "archived_z4_reuse_used": False,
            "N_gap_forced_to_density": False,
        }
        if write_output:
            output_path.parent.mkdir(parents=True, exist_ok=True)
            output_path.write_text(json.dumps(normalized, indent=2), encoding="utf-8")
    ready = normalized is not None
    return {
        "status": "janus-z2-global-bimetric-state-to-flrw-sector-normalization-gate",
        "input_path": str(input_path),
        "output_path": str(output_path),
        "input_exists": state is not None,
        "validation_errors": errors,
        "rho_plus0_derived": ready,
        "rho_minus0_derived": ready,
        "sector_normalizations_ready": ready,
        "normalized_sector_payload": normalized,
        "gate_passed": ready,
        "primary_blocker": "none" if ready else errors[0],
        "next_required": []
        if ready
        else [
            "derive_global_bimetric_stress_energy_state_inputs",
            "include rho_plus_kg_m3 with active provenance",
            "prove PT_energy_sign_reversal",
        ],
    }


def write_reports() -> dict[str, Any]:
    payload = build_payload(write_output=True)
    JSON_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2 Global Bimetric State To FLRW Sector Normalization Gate",
        "",
        f"Input exists: `{payload['input_exists']}`",
        f"Sector normalizations ready: `{payload['sector_normalizations_ready']}`",
        f"Primary blocker: `{payload['primary_blocker']}`",
        "",
        "## Next Required",
    ]
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
