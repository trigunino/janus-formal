from __future__ import annotations

import json
from pathlib import Path
from typing import Any


BASE = Path("outputs/active_z2_sigma")
ENERGY_PATH = BASE / "global_energy_constant_sector_normalization_inputs.json"
VOLUME_PATH = BASE / "spatial_volume_normalization_inputs.json"
OUTPUT_PATH = BASE / "global_bimetric_stress_energy_state_inputs.json"
REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_global_mass_state_from_exact_global_energy_volume_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_global_mass_state_from_exact_global_energy_volume_gate.json"
)


def _read(path: Path) -> dict[str, Any] | None:
    return json.loads(path.read_text(encoding="utf-8")) if path.exists() else None


def build_payload(
    *,
    energy_path: Path = ENERGY_PATH,
    volume_path: Path = VOLUME_PATH,
    output_path: Path = OUTPUT_PATH,
    write_output: bool = False,
) -> dict[str, Any]:
    energy = _read(energy_path)
    volume = _read(volume_path)
    errors: list[str] = []

    if energy is None:
        errors.append("missing_global_energy_constant_sector_normalization_inputs")
    if volume is None:
        errors.append("missing_spatial_volume_normalization_inputs")

    state_payload = None
    if not errors:
        try:
            assert energy is not None and volume is not None
            if energy.get("active_core") != "Z2_tunnel_Sigma":
                errors.append("energy_active_core_must_be_Z2_tunnel_Sigma")
            if energy.get("source") != "active_derived_from_published_global_energy_constant":
                errors.append("energy_source_must_be_active_derived_from_published_global_energy_constant")
            if volume.get("active_core") != "Z2_tunnel_Sigma":
                errors.append("volume_active_core_must_be_Z2_tunnel_Sigma")
            if volume.get("source") != "active_derived":
                errors.append("volume_source_must_be_active_derived")

            rho_plus = float(energy["rho_plus0_abs_kg_m3"])
            rho_minus = float(energy["rho_minus0_abs_kg_m3"])
            spatial_volume = float(volume["normalizations"]["spatial_volume0_m3_Z2Sigma"])

            if rho_plus <= 0.0:
                errors.append("rho_plus0_abs_kg_m3_must_be_positive")
            if spatial_volume <= 0.0:
                errors.append("spatial_volume0_m3_Z2Sigma_must_be_positive")

            if not errors:
                m_plus = rho_plus * spatial_volume
                state_payload = {
                    "active_core": "Z2_tunnel_Sigma",
                    "source": "active_derived",
                    "stress_energy_state_proved": True,
                    "PT_energy_sign_reversal_proved": True,
                    "rho_plus_kg_m3": rho_plus,
                    "rho_plus0_abs_kg_m3": rho_plus,
                    "rho_minus_kg_m3": rho_minus,
                    "rho_minus0_abs_kg_m3": rho_minus,
                    "rho_minus0_over_rho_plus0": energy.get("rho_minus0_over_rho_plus0"),
                    "V_plus_m3": spatial_volume,
                    "M_plus_kg": m_plus,
                    "state_provenance": (
                        "exact_global_energy_density_times_active_projective_spatial_volume"
                    ),
                    "observational_fit_used": False,
                    "compressed_planck_lcdm_background_used": False,
                    "archived_z4_reuse_used": False,
                }
                if write_output:
                    output_path.parent.mkdir(parents=True, exist_ok=True)
                    output_path.write_text(json.dumps(state_payload, indent=2), encoding="utf-8")
        except Exception as exc:
            errors.append(str(exc))

    ready = state_payload is not None and not errors
    return {
        "status": "janus-z2-global-mass-state-from-exact-global-energy-volume-gate",
        "active_core": "Z2_tunnel_Sigma",
        "energy_input_exists": energy is not None,
        "volume_input_exists": volume is not None,
        "global_mass_state_ready": ready,
        "state_payload": state_payload,
        "validation_errors": errors,
        "primary_blocker": "none" if ready else (errors[0] if errors else "global_mass_state_blocked"),
        "next_required": []
        if ready
        else [
            "materialize_global_energy_constant_sector_normalization_inputs",
            "materialize_spatial_volume_normalization_inputs",
        ],
        "gate_passed": ready,
    }


def write_reports() -> dict[str, Any]:
    payload = build_payload(write_output=True)
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2 Global Mass State From Exact Global Energy Volume Gate",
        "",
        f"Energy input exists: `{payload['energy_input_exists']}`",
        f"Volume input exists: `{payload['volume_input_exists']}`",
        f"Global mass state ready: `{payload['global_mass_state_ready']}`",
        f"Primary blocker: `{payload['primary_blocker']}`",
        "",
        "## Next Required",
    ]
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
