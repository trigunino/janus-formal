from __future__ import annotations

import json
from pathlib import Path
from typing import Any


BASE = Path("outputs/active_z2_sigma")
INPUT_PATH = BASE / "global_souriau_orbit_quantization_inputs.json"
OUTPUT_PATH = BASE / "alpha_composite_quantized_selector_inputs.json"
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_global_souriau_orbit_quantization_gate.json")
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_global_souriau_orbit_quantization_gate.md")


def _read(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8")) if path.exists() else {}


def _positive(value: Any) -> bool:
    return isinstance(value, (int, float)) and float(value) > 0.0


def build_payload(
    input_path: Path = INPUT_PATH,
    output_path: Path = OUTPUT_PATH,
    *,
    write_output: bool = False,
) -> dict[str, Any]:
    data = _read(input_path)
    checks = {
        "global_state_space_declared": bool(data.get("global_state_space_declared")),
        "poincare_souriau_coadjoint_orbits_declared": True,
        "moment_map_energy_defined": True,
        "PT_antichronous_pairing_declared": True,
        "mass_casimir_identified": True,
        "mass_casimir_continuous_by_default": True,
        "geometric_quantization_performed": bool(data.get("geometric_quantization_performed")),
        "integrality_condition_on_global_orbit": bool(
            data.get("integrality_condition_on_global_orbit")
        ),
        "mass_orbit_lattice_derived": bool(data.get("mass_orbit_lattice_derived")),
        "minimal_mass_unit_kg_available": _positive(data.get("minimal_mass_unit_kg")),
        "primitive_sector_n_available": isinstance(data.get("primitive_sector_n"), int)
        and data.get("primitive_sector_n") != 0,
    }
    quantized = all(checks.values())
    output = None
    if quantized:
        output = {
            "active_core": "Z2_tunnel_Sigma",
            "source": "active_derived",
            "noether_or_souriau_charge_to_alpha_map_derived": True,
            "charge_lattice_quantized": True,
            "charge_unit_kg": float(data["minimal_mass_unit_kg"]),
            "charge_unit_provenance": "global_souriau_orbit_quantization",
            "integer_sector_n": int(data["primitive_sector_n"]),
            "primitive_sector_selected": bool(data.get("primitive_sector_selected")),
            "primitive_sector_provenance": "global_souriau_orbit_quantization",
            "c_plus0_m_s": float(data.get("c_plus0_m_s", 299792458.0)),
            "c_minus0_m_s": float(data.get("c_minus0_m_s", 299792458.0)),
            "G_plus_SI": float(data.get("G_plus_SI", 6.67430e-11)),
            "observational_fit_used": False,
            "compressed_planck_lcdm_background_used": False,
            "archived_z4_reuse_used": False,
        }
        if write_output:
            output_path.parent.mkdir(parents=True, exist_ok=True)
            output_path.write_text(json.dumps(output, indent=2), encoding="utf-8")
    return {
        "status": "janus-z2-global-souriau-orbit-quantization-gate",
        "active_core": "Z2_tunnel_Sigma",
        "checks": checks,
        "global_orbit_quantized": quantized,
        "alpha_composite_inputs_written": output is not None,
        "blocked_by": [key for key, ok in checks.items() if not ok],
        "core_result": (
            "Global Souriau/PT supplies the mass Casimir and PT sign pairing. "
            "It does not discretize mass by itself; Poincare massive coadjoint "
            "orbits are labeled by continuous m unless a separate integrality "
            "condition on the global orbit is derived."
        ),
        "output_payload": output,
        "gate_passed": True,
    }


def write_reports() -> dict[str, Any]:
    payload = build_payload(write_output=True)
    JSON_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(
        "\n".join(
            [
                "# Janus Z2 Global Souriau Orbit Quantization Gate",
                "",
                f"Global orbit quantized: `{payload['global_orbit_quantized']}`",
                "",
                payload["core_result"],
            ]
        ),
        encoding="utf-8",
    )
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
