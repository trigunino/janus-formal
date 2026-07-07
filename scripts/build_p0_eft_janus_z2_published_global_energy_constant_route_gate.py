from __future__ import annotations

import json
import math
from pathlib import Path
from typing import Any


BASE = Path("outputs/active_z2_sigma")
INPUT_PATH = BASE / "published_global_energy_constant_inputs.json"
RATIO_PATH = BASE / "published_bimetric_sector_ratio_inputs.json"
OUTPUT_PATH = BASE / "global_energy_constant_sector_normalization_inputs.json"
REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_published_global_energy_constant_route_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_published_global_energy_constant_route_gate.json"
)
FORBIDDEN = ("fit", "planck", "lcdm", "bao", "z4", "demo")


def _read(path: Path) -> dict[str, Any] | None:
    return json.loads(path.read_text(encoding="utf-8")) if path.exists() else None


def _bad_provenance(value: Any) -> bool:
    text = str(value or "").strip().lower()
    return not text or any(token in text for token in FORBIDDEN)


def _finite(value: Any) -> bool:
    return isinstance(value, (int, float)) and math.isfinite(float(value))


def _ratio(ratio: dict[str, Any] | None) -> float | None:
    if ratio is None:
        return None
    raw = ratio.get("rho_minus0_over_rho_plus0")
    if raw is None:
        raw = ratio.get("normalizations", {}).get("rho_minus0_over_rho_plus0")
    return float(raw) if raw is not None else None


def _validate_input(data: dict[str, Any]) -> list[str]:
    errors: list[str] = []
    if data.get("active_core") != "Z2_tunnel_Sigma":
        errors.append("active_core_must_be_Z2_tunnel_Sigma")
    if data.get("source") != "published_janus_exact_global_energy_state":
        errors.append("source_must_be_published_janus_exact_global_energy_state")
    if data.get("global_energy_constant_proved") is not True:
        errors.append("global_energy_constant_must_be_proved")
    if _bad_provenance(data.get("global_energy_provenance")):
        errors.append("global_energy_provenance_missing_or_forbidden")
    for key in [
        "E_global_J",
        "c_plus0_m_s",
        "c_minus0_m_s",
        "a_plus0_weight",
        "a_minus0_weight",
    ]:
        if not _finite(data.get(key)):
            errors.append(f"{key}_missing_or_nonfinite")
    for key in [
        "observational_fit_used",
        "compressed_planck_lcdm_background_used",
        "archived_z4_reuse_used",
    ]:
        if data.get(key) is True:
            errors.append(f"forbidden_flag:{key}")
    return errors


def build_payload(
    *,
    input_path: Path = INPUT_PATH,
    ratio_path: Path = RATIO_PATH,
    output_path: Path = OUTPUT_PATH,
    write_output: bool = False,
) -> dict[str, Any]:
    data = _read(input_path)
    ratio_payload = _read(ratio_path)
    ratio = _ratio(ratio_payload)
    errors = ["missing_published_global_energy_constant_inputs"] if data is None else _validate_input(data)
    if ratio is None:
        errors.append("missing_published_sector_ratio")

    normalized = None
    denominator = None
    if data is not None and ratio is not None and not errors:
        denominator = (
            float(data["c_plus0_m_s"]) ** 2 * float(data["a_plus0_weight"])
            + ratio * float(data["c_minus0_m_s"]) ** 2 * float(data["a_minus0_weight"])
        )
        if denominator == 0.0:
            errors.append("global_energy_denominator_zero")
        else:
            rho_plus = float(data["E_global_J"]) / denominator
            rho_minus = ratio * rho_plus
            if rho_plus <= 0.0:
                errors.append("rho_plus0_not_positive_from_global_energy")
            else:
                normalized = {
                    "active_core": "Z2_tunnel_Sigma",
                    "source": "active_derived_from_published_global_energy_constant",
                    "rho_plus0_abs_kg_m3": rho_plus,
                    "rho_minus0_abs_kg_m3": rho_minus,
                    "rho_minus0_over_rho_plus0": ratio,
                    "global_energy_formula": (
                        "E = rho_plus0*c_plus0^2*w_plus0 + "
                        "rho_minus0*c_minus0^2*w_minus0"
                    ),
                    "global_energy_provenance": data["global_energy_provenance"],
                    "observational_fit_used": False,
                    "compressed_planck_lcdm_background_used": False,
                    "archived_z4_reuse_used": False,
                }
                if write_output:
                    output_path.parent.mkdir(parents=True, exist_ok=True)
                    output_path.write_text(json.dumps(normalized, indent=2), encoding="utf-8")

    ready = normalized is not None
    return {
        "status": "janus-z2-published-global-energy-constant-route-gate",
        "active_core": "Z2_tunnel_Sigma",
        "published_anchor": "The Janus Cosmological Model pages 80 and 232: exact bimetric FLRW solution with conserved E and relative 5/95 split.",
        "route_statement": (
            "This is how the published Janus cosmology can close a density scale: "
            "not from local Sigma topology, but from a dimensional global energy "
            "state constant of the bimetric FLRW solution."
        ),
        "input_path": str(input_path),
        "ratio_path": str(ratio_path),
        "output_path": str(output_path),
        "input_exists": data is not None,
        "ratio_exists": ratio_payload is not None,
        "rho_minus0_over_rho_plus0": ratio,
        "global_energy_denominator": denominator,
        "global_energy_constant_route_ready": ready,
        "normalized_sector_payload": normalized,
        "validation_errors": errors,
        "why_Z4_did_not_solve_this": (
            "Archived Z4 branches moved dimensionless CMB/BAO response parameters; "
            "they did not derive a dimensional global matter state."
        ),
        "forbidden_shortcuts": [
            "use_observational_density_as_E_global",
            "set_E_global_to_zero_to_force_nonzero_density",
            "reuse_archived_Z4_effective_parameters",
        ],
        "next_required": []
        if ready
        else [
            "derive_or_supply_published_global_energy_constant_inputs",
            "include E_global_J with active non-observational provenance",
            "include present bimetric weights a_plus0_weight/a_minus0_weight",
        ],
        "gate_passed": ready,
    }


def write_reports() -> dict[str, Any]:
    payload = build_payload(write_output=True)
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2 Published Global Energy Constant Route Gate",
        "",
        payload["route_statement"],
        "",
        f"Input exists: `{payload['input_exists']}`",
        f"Ratio exists: `{payload['ratio_exists']}`",
        f"Route ready: `{payload['global_energy_constant_route_ready']}`",
        f"Validation errors: `{payload['validation_errors']}`",
        "",
        "## Next Required",
    ]
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
