from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from janus_lab.z2_sigma_early_plasma_inputs import (
    assemble_active_z2sigma_early_plasma_input_manifest,
)


BARYON_PHOTON_PATH = Path("outputs/active_z2_sigma/early_plasma_baryon_photon_inputs.json")
IONIZATION_THOMSON_PATH = Path("outputs/active_z2_sigma/early_plasma_ionization_thomson_inputs.json")
OUTPUT_PATH = Path("outputs/active_z2_sigma/early_plasma_inputs.json")
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_early_plasma_inputs_assembler_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_early_plasma_inputs_assembler_gate.json")


def _read_json(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def build_payload(
    *,
    baryon_photon_path: Path = BARYON_PHOTON_PATH,
    ionization_thomson_path: Path = IONIZATION_THOMSON_PATH,
    output_path: Path = OUTPUT_PATH,
) -> dict:
    baryon_photon_exists = baryon_photon_path.exists()
    ionization_thomson_exists = ionization_thomson_path.exists()
    output_written = False
    validation_error = None
    if baryon_photon_exists and ionization_thomson_exists:
        try:
            assembled = assemble_active_z2sigma_early_plasma_input_manifest(
                baryon_photon_payload=_read_json(baryon_photon_path),
                ionization_thomson_payload=_read_json(ionization_thomson_path),
            )
            output_path.parent.mkdir(parents=True, exist_ok=True)
            output_path.write_text(json.dumps(assembled, indent=2), encoding="utf-8")
            output_written = True
        except Exception as exc:
            validation_error = str(exc)
    return {
        "status": "janus-z2-sigma-early-plasma-inputs-assembler-gate",
        "active_core": "Z2_tunnel_Sigma",
        "baryon_photon_input_manifest": str(baryon_photon_path),
        "ionization_thomson_input_manifest": str(ionization_thomson_path),
        "output_manifest": str(output_path),
        "baryon_photon_input_exists": baryon_photon_exists,
        "ionization_thomson_input_exists": ionization_thomson_exists,
        "early_plasma_inputs_written": output_written,
        "uses_compressed_planck_lcdm_rd": False,
        "uses_archived_z4_inputs": False,
        "uses_phenomenological_holst_bao_scan": False,
        "gate_passed": output_written,
        "primary_blocker": (
            "none" if output_written else "baryon_photon_and_ionization_thomson_inputs"
        ),
        "validation_error": validation_error,
        "next_required": [
            "supply_outputs_active_z2_sigma_early_plasma_baryon_photon_inputs_json",
            "supply_outputs_active_z2_sigma_early_plasma_ionization_thomson_inputs_json",
            "run_early_plasma_manifest_writer_from_inputs_gate",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Early-Plasma Inputs Assembler Gate",
        "",
        f"Baryon/photon input exists: `{payload['baryon_photon_input_exists']}`",
        f"Ionization/Thomson input exists: `{payload['ionization_thomson_input_exists']}`",
        f"Early-plasma inputs written: `{payload['early_plasma_inputs_written']}`",
        f"Gate passed: `{payload['gate_passed']}`",
    ]
    if payload["validation_error"]:
        lines.extend(["", "## Validation Error", payload["validation_error"]])
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
