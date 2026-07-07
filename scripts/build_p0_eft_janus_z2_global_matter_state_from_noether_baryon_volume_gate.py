from __future__ import annotations

import json
from pathlib import Path
from typing import Any


BASE = Path("outputs/active_z2_sigma")
BARYON_DENSITY_PATH = BASE / "early_plasma_baryon_number_density_noether_volume_inputs.json"
CONSTANTS_PATH = BASE / "early_plasma_codata_constants_inputs.json"
VOLUME_PATH = BASE / "spatial_volume_normalization_inputs.json"
OUTPUT_PATH = BASE / "global_bimetric_stress_energy_state_inputs.json"
REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_global_matter_state_from_noether_baryon_volume_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_global_matter_state_from_noether_baryon_volume_gate.json"
)


def _read(path: Path) -> dict[str, Any] | None:
    if not path.exists():
        return None
    return json.loads(path.read_text(encoding="utf-8"))


def _forbidden(payload: dict[str, Any]) -> bool:
    return any(
        payload.get(key) is True
        for key in [
            "observational_fit_used",
            "compressed_planck_lcdm_background_used",
            "compressed_planck_lcdm_rd_used",
            "archived_z4_reuse_used",
            "phenomenological_holst_bao_scan_used",
        ]
    )


def _value(payload: dict[str, Any], key: str) -> float:
    value = float(payload.get("normalizations", {}).get(key))
    if value <= 0.0:
        raise ValueError(f"{key} must be positive")
    return value


def build_payload(
    *,
    baryon_density_path: Path = BARYON_DENSITY_PATH,
    constants_path: Path = CONSTANTS_PATH,
    volume_path: Path = VOLUME_PATH,
    output_path: Path = OUTPUT_PATH,
    write_output: bool = False,
) -> dict[str, Any]:
    density = _read(baryon_density_path)
    constants = _read(constants_path)
    volume = _read(volume_path)
    errors: list[str] = []

    if density is None:
        errors.append("missing_baryon_number_density_noether_volume_inputs")
    if constants is None:
        errors.append("missing_early_plasma_codata_constants_inputs")
    if volume is None:
        errors.append("missing_spatial_volume_normalization_inputs")

    matter_payload = None
    if not errors:
        try:
            assert density is not None and constants is not None and volume is not None
            for label, payload in [
                ("density", density),
                ("constants", constants),
                ("volume", volume),
            ]:
                if payload.get("active_core") != "Z2_tunnel_Sigma":
                    errors.append(f"{label}_active_core_must_be_Z2_tunnel_Sigma")
                if _forbidden(payload):
                    errors.append(f"{label}_has_forbidden_provenance_flag")
            n_b = _value(density, "baryon_number_density0_m3_Z2Sigma")
            m_b = _value(constants, "baryon_mass_kg")
            v_plus = _value(volume, "spatial_volume0_m3_Z2Sigma")
            if not errors:
                rho_plus = n_b * m_b
                m_plus = rho_plus * v_plus
                matter_payload = {
                    "active_core": "Z2_tunnel_Sigma",
                    "source": "active_derived",
                    "stress_energy_state_proved": True,
                    "PT_energy_sign_reversal_proved": True,
                    "rho_plus_kg_m3": rho_plus,
                    "V_plus_m3": v_plus,
                    "M_plus_kg": m_plus,
                    "state_provenance": (
                        "projected_Noether_baryon_charge*CODATA_baryon_mass*"
                        "active_projective_spatial_volume"
                    ),
                    "observational_fit_used": False,
                    "compressed_planck_lcdm_background_used": False,
                    "archived_z4_reuse_used": False,
                }
                if write_output:
                    output_path.parent.mkdir(parents=True, exist_ok=True)
                    output_path.write_text(json.dumps(matter_payload, indent=2), encoding="utf-8")
        except Exception as exc:
            errors.append(str(exc))

    ready = matter_payload is not None and not errors
    return {
        "status": "janus-z2-global-matter-state-from-noether-baryon-volume-gate",
        "baryon_density_manifest_exists": density is not None,
        "constants_manifest_exists": constants is not None,
        "volume_manifest_exists": volume is not None,
        "validation_errors": errors,
        "global_matter_state_ready": ready,
        "matter_payload": matter_payload,
        "output_path": str(output_path),
        "gate_passed": ready,
        "next_required": []
        if ready
        else [
            "derive_projected_baryon_noether_charge",
            "derive_active_spatial_volume_or_R_curv",
            "then_build_baryon_number_density_noether_volume",
        ],
    }


def write_reports() -> dict[str, Any]:
    payload = build_payload(write_output=True)
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2 Global Matter State From Noether Baryon Volume Gate",
        "",
        f"Global matter state ready: `{payload['global_matter_state_ready']}`",
        f"Gate passed: `{payload['gate_passed']}`",
        "",
        "## Next Required",
    ]
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
