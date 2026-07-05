from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z2_sigma_baryon_number_density_noether_volume_gate import (
    build_payload as build_baryon_number_density_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_early_plasma_manifest_writer_from_inputs_gate import (
    build_payload as build_manifest_writer_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_early_plasma_saha_inputs_assembler_gate import (
    build_payload as build_saha_inputs_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_saha_ionization_history_gate import (
    build_payload as build_saha_history_payload,
)


CHARGE_PATH = Path("outputs/active_z2_sigma/projected_baryon_noether_charge_inputs.json")
VOLUME_PATH = Path("outputs/active_z2_sigma/spatial_volume_normalization_inputs.json")
CONSTANTS_PATH = Path("outputs/active_z2_sigma/early_plasma_codata_constants_inputs.json")
TEMPERATURE_PATH = Path("outputs/active_z2_sigma/early_plasma_photon_temperature_firas_inputs.json")
BARYON_DENSITY_PATH = Path(
    "outputs/active_z2_sigma/early_plasma_baryon_number_density_noether_volume_inputs.json"
)
SAHA_HISTORY_PATH = Path("outputs/active_z2_sigma/early_plasma_saha_ionization_history_inputs.json")
EARLY_PLASMA_INPUTS_PATH = Path("outputs/active_z2_sigma/early_plasma_inputs.json")
EARLY_PLASMA_MANIFEST_PATH = Path("outputs/active_z2_sigma/early_plasma.json")
REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_noether_volume_to_saha_early_plasma_pipeline_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_noether_volume_to_saha_early_plasma_pipeline_gate.json"
)


def build_payload(
    *,
    charge_path: Path = CHARGE_PATH,
    volume_path: Path = VOLUME_PATH,
    constants_path: Path = CONSTANTS_PATH,
    temperature_path: Path = TEMPERATURE_PATH,
    baryon_density_path: Path = BARYON_DENSITY_PATH,
    saha_history_path: Path = SAHA_HISTORY_PATH,
    early_plasma_inputs_path: Path = EARLY_PLASMA_INPUTS_PATH,
    early_plasma_manifest_path: Path = EARLY_PLASMA_MANIFEST_PATH,
    write_output: bool = True,
) -> dict:
    baryon_density = build_baryon_number_density_payload(
        charge_path=charge_path,
        volume_path=volume_path,
        output_path=baryon_density_path,
    )
    saha_history = build_saha_history_payload(
        baryon_input_path=baryon_density_path,
        temperature_input_path=temperature_path,
        constants_input_path=constants_path,
        output_path=saha_history_path,
        write_output=write_output,
    )
    saha_inputs = build_saha_inputs_payload(
        constants_path=constants_path,
        temperature_path=temperature_path,
        saha_history_path=saha_history_path,
        output_path=early_plasma_inputs_path,
        write_output=write_output,
    )
    manifest = build_manifest_writer_payload(
        input_path=early_plasma_inputs_path,
        manifest_path=early_plasma_manifest_path,
    )
    gate_passed = (
        baryon_density["gate_passed"]
        and saha_history["gate_passed"]
        and saha_inputs["gate_passed"]
        and manifest["gate_passed"]
    )
    primary_blocker = (
        "none"
        if gate_passed
        else baryon_density.get("primary_blocker")
        or saha_history.get("primary_blocker")
        or saha_inputs.get("primary_blocker")
        or manifest.get("primary_blocker")
        or "early_plasma_manifest_from_active_baryon_photon_saha_inputs"
    )
    return {
        "status": "janus-z2-sigma-noether-volume-to-saha-early-plasma-pipeline-gate",
        "active_core": "Z2_tunnel_Sigma",
        "projected_charge_manifest": str(charge_path),
        "spatial_volume_manifest": str(volume_path),
        "baryon_density_manifest": str(baryon_density_path),
        "saha_history_manifest": str(saha_history_path),
        "early_plasma_inputs_manifest": str(early_plasma_inputs_path),
        "early_plasma_manifest": str(early_plasma_manifest_path),
        "baryon_density_passed": baryon_density["gate_passed"],
        "saha_history_passed": saha_history["gate_passed"],
        "saha_inputs_passed": saha_inputs["gate_passed"],
        "early_plasma_manifest_passed": manifest["gate_passed"],
        "upstream_frontiers": {
            "baryon_density": {
                "gate": baryon_density["status"],
                "passed": baryon_density["gate_passed"],
                "projected_charge_manifest_exists": baryon_density[
                    "projected_charge_manifest_exists"
                ],
                "spatial_volume_manifest_exists": baryon_density[
                    "spatial_volume_manifest_exists"
                ],
                "projected_baryon_charge_gate_passed": baryon_density[
                    "projected_baryon_charge_gate_passed"
                ],
                "spatial_volume_projective_slice_gate_passed": baryon_density[
                    "spatial_volume_projective_slice_gate_passed"
                ],
                "upstream_frontiers": baryon_density.get("upstream_frontiers", {}),
                "nearest_frontier": baryon_density.get(
                    "nearest_baryon_density_frontier", {}
                ),
                "primary_blocker": baryon_density.get("primary_blocker"),
            },
            "saha_history": {
                "gate": saha_history["status"],
                "passed": saha_history["gate_passed"],
                "baryon_input_valid": saha_history["baryon_input_valid"],
                "temperature_input_valid": saha_history["temperature_input_valid"],
                "codata_constants_valid": saha_history["codata_constants_valid"],
                "upstream_frontiers": saha_history.get("upstream_frontiers", {}),
                "nearest_frontier": saha_history.get("nearest_saha_history_frontier", {}),
                "primary_blocker": saha_history.get("primary_blocker"),
            },
            "saha_inputs": {
                "gate": saha_inputs["status"],
                "passed": saha_inputs["gate_passed"],
                "constants_valid": saha_inputs["constants_valid"],
                "temperature_valid": saha_inputs["temperature_valid"],
                "saha_history_valid": saha_inputs["saha_history_valid"],
                "primary_blocker": saha_inputs.get("primary_blocker"),
            },
            "early_plasma_manifest": {
                "gate": manifest["status"],
                "passed": manifest["gate_passed"],
                "input_exists": manifest["input_exists"],
                "input_valid": manifest["input_valid"],
                "primary_blocker": manifest.get("primary_blocker"),
            },
        },
        "nearest_noether_volume_plasma_frontier": {
            "blocks": [
                "projected_baryon_number_charge_Z2Sigma",
                "active_spatial_volume0_Z2Sigma",
                "Saha_ionization_history",
                "early_plasma_manifest",
            ],
            "diagnostic_only": True,
        },
        "uses_compressed_planck_lcdm_rd": False,
        "uses_archived_z4_inputs": False,
        "uses_phenomenological_holst_bao_scan": False,
        "gate_passed": gate_passed,
        "primary_blocker": primary_blocker,
        "blocker": None
        if gate_passed
        else "missing active projected baryon charge, active spatial volume, or derived Saha/plasma inputs",
        "next_required": [
            "derive_projected_baryon_number_charge_Z2Sigma",
            "derive_active_spatial_volume0_Z2Sigma",
            "run_thomson_drag_rate_builder_gate",
            "combine_Gamma_drag_Z2Sigma_with_active_H_Z2Sigma_for_z_d",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(
        "\n".join(
            [
                "# Janus Z2/Sigma Noether/Volume to Saha Early-Plasma Pipeline Gate",
                "",
                f"Baryon density passed: `{payload['baryon_density_passed']}`",
                f"Saha history passed: `{payload['saha_history_passed']}`",
                f"Saha inputs passed: `{payload['saha_inputs_passed']}`",
                f"Early-plasma manifest passed: `{payload['early_plasma_manifest_passed']}`",
                f"Gate passed: `{payload['gate_passed']}`",
            ]
        ),
        encoding="utf-8",
    )
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
