from __future__ import annotations

import json
import math
from pathlib import Path
from typing import Any


BASE = Path("outputs/active_z2_sigma")
INPUT_PATH = BASE / "alpha_composite_quantized_selector_inputs.json"
OUTPUT_PATH = BASE / "exact_solution_alpha_state_sector_inputs.json"
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_alpha_composite_quantized_selector_gate.json")
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_alpha_composite_quantized_selector_gate.md")
FORBIDDEN = ("fit", "planck", "lcdm", "bao", "z4", "demo")


def _read(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8")) if path.exists() else {}


def _clean(value: Any) -> bool:
    text = str(value or "").strip().lower()
    return bool(text) and not any(token in text for token in FORBIDDEN)


def _positive(value: Any) -> bool:
    return isinstance(value, (int, float)) and math.isfinite(float(value)) and float(value) > 0


def _nonzero_int(value: Any) -> bool:
    return isinstance(value, int) and value != 0


def alpha_from_quantized_mass_unit(n: int, charge_unit_kg: float, g_si: float, c_m_s: float) -> float:
    if n == 0 or charge_unit_kg <= 0 or g_si <= 0 or c_m_s <= 0:
        raise ValueError("n, charge_unit_kg, G and c must be nonzero/positive")
    return 2.0 * math.pi * g_si * abs(n) * charge_unit_kg / c_m_s**2


def build_payload(
    input_path: Path = INPUT_PATH,
    output_path: Path = OUTPUT_PATH,
    *,
    write_output: bool = False,
) -> dict[str, Any]:
    data = _read(input_path)
    checks = {
        "active_core_Z2_tunnel_Sigma": data.get("active_core") == "Z2_tunnel_Sigma",
        "source_active_derived": data.get("source") == "active_derived",
        "noether_or_souriau_charge_to_alpha_map_derived": bool(
            data.get("noether_or_souriau_charge_to_alpha_map_derived")
        ),
        "charge_lattice_quantized": bool(data.get("charge_lattice_quantized")),
        "charge_unit_kg_available": _positive(data.get("charge_unit_kg")),
        "charge_unit_provenance_clean": _clean(data.get("charge_unit_provenance")),
        "integer_sector_n_available": _nonzero_int(data.get("integer_sector_n")),
        "primitive_sector_selected": bool(data.get("primitive_sector_selected")),
        "primitive_sector_provenance_clean": _clean(data.get("primitive_sector_provenance")),
        "c_plus0_available": _positive(data.get("c_plus0_m_s")),
        "c_minus0_available": _positive(data.get("c_minus0_m_s")),
        "G_plus_available": _positive(data.get("G_plus_SI")),
        "no_observational_fit": data.get("observational_fit_used") is not True,
        "no_compressed_lcdm": data.get("compressed_planck_lcdm_background_used") is not True,
        "no_legacy_z4": data.get("archived_z4_reuse_used") is not True,
    }
    spectrum_ready = all(
        checks[key]
        for key in [
            "active_core_Z2_tunnel_Sigma",
            "source_active_derived",
            "noether_or_souriau_charge_to_alpha_map_derived",
            "charge_lattice_quantized",
            "charge_unit_kg_available",
            "charge_unit_provenance_clean",
            "integer_sector_n_available",
            "c_plus0_available",
            "c_minus0_available",
            "G_plus_available",
            "no_observational_fit",
            "no_compressed_lcdm",
            "no_legacy_z4",
        ]
    )
    unique_ready = spectrum_ready and checks["primitive_sector_selected"] and checks[
        "primitive_sector_provenance_clean"
    ]
    output = None
    if spectrum_ready:
        alpha_m = alpha_from_quantized_mass_unit(
            int(data["integer_sector_n"]),
            float(data["charge_unit_kg"]),
            float(data["G_plus_SI"]),
            float(data["c_plus0_m_s"]),
        )
        output = {
            "active_core": "Z2_tunnel_Sigma",
            "source": "exact_solution_integration_constant_state",
            "alpha_m": alpha_m,
            "alpha_state_provenance": (
                "composite_quantized_charge_selector:"
                f"{data['charge_unit_provenance']}:n={int(data['integer_sector_n'])}"
            ),
            "alpha_sector_declared_not_derived": not unique_ready,
            "full_no_fit_prediction_ready": bool(unique_ready),
            "c_plus0_m_s": float(data["c_plus0_m_s"]),
            "c_minus0_m_s": float(data["c_minus0_m_s"]),
            "G_plus_SI": float(data["G_plus_SI"]),
            "a_plus0_weight": float(data.get("a_plus0_weight", 1.0)),
            "a_minus0_weight": float(data.get("a_minus0_weight", 1.0)),
            "observational_fit_used": False,
            "compressed_planck_lcdm_background_used": False,
            "archived_z4_reuse_used": False,
        }
        if write_output:
            output_path.parent.mkdir(parents=True, exist_ok=True)
            output_path.write_text(json.dumps(output, indent=2), encoding="utf-8")
    return {
        "status": "janus-z2-alpha-composite-quantized-selector-gate",
        "active_core": "Z2_tunnel_Sigma",
        "input_path": str(input_path),
        "output_path": str(output_path),
        "checks": checks,
        "alpha_spectrum_ready": spectrum_ready,
        "unique_alpha_selector_ready": unique_ready,
        "formula": "alpha_n = 2*pi*G*|n|*m_charge/c^2",
        "state_payload": output,
        "blocked_by": [key for key, ok in checks.items() if not ok],
        "interpretation": (
            "The composite route can quantize alpha only if a Noether/Souriau "
            "charge unit is derived. It becomes a unique no-fit selector only "
            "if a primitive sector law also fixes n."
        ),
        "gate_passed": True,
    }


def write_reports() -> dict[str, Any]:
    payload = build_payload(write_output=True)
    JSON_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2 Alpha Composite Quantized Selector Gate",
        "",
        f"Alpha spectrum ready: `{payload['alpha_spectrum_ready']}`",
        f"Unique alpha selector ready: `{payload['unique_alpha_selector_ready']}`",
        f"Formula: `{payload['formula']}`",
        "",
        payload["interpretation"],
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
