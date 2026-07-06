from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from janus_lab.z2_sigma_matter_flux import build_transparent_matter_flux_component_payload
from scripts.build_p0_eft_janus_z2_sigma_matter_flux_transparency_input_writer_gate import (
    build_payload as build_transparency_input_writer_payload,
)


INPUT_PATH = Path("outputs/active_z2_sigma/matter_flux_transparency_inputs.json")
OUTPUT_PATH = Path("outputs/active_z2_sigma/matter_flux_zero_components.json")
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_matter_flux_zero_component_from_transparency_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_matter_flux_zero_component_from_transparency_gate.json")


def _load_input(path: Path) -> dict:
    payload = json.loads(path.read_text(encoding="utf-8"))
    if payload.get("active_core") != "Z2_tunnel_Sigma":
        raise ValueError("Manifest active_core must be Z2_tunnel_Sigma")
    if payload.get("source") != "active_derived":
        raise ValueError("Manifest source must be active_derived")
    for key in [
        "compressed_planck_lcdm_background_used",
        "archived_z4_reuse_used",
        "phenomenological_holst_bao_scan_used",
    ]:
        if payload.get(key) is not False:
            raise ValueError(f"Forbidden provenance flag must be false: {key}")
    return payload


def build_payload(
    *,
    input_path: Path = INPUT_PATH,
    output_path: Path = OUTPUT_PATH,
    auto_write_input: bool = True,
) -> dict:
    transparency_writer = (
        build_transparency_input_writer_payload(output_path=input_path)
        if auto_write_input
        else {
            "status": "janus-z2-sigma-matter-flux-transparency-input-writer-gate",
            "gate_passed": False,
            "grid_source_exists": False,
            "active_sigma_transparency_derived": False,
            "upstream_frontiers": {},
            "nearest_transparency_input_frontier": {"diagnostic_only": True},
        }
    )
    input_exists = input_path.exists()
    input_valid = False
    output_written = False
    values_ready = False
    validation_error = None
    if input_exists:
        try:
            source = _load_input(input_path)
            component_payload = build_transparent_matter_flux_component_payload(
                a_grid=source["a_grid"],
                active_sigma_transparency_derived=source["active_sigma_transparency_derived"],
                transparency_provenance=source["transparency_provenance"],
            )
            input_valid = True
            values_ready = True
            output_path.parent.mkdir(parents=True, exist_ok=True)
            output_path.write_text(json.dumps(component_payload, indent=2), encoding="utf-8")
            output_written = True
        except Exception as exc:
            validation_error = str(exc)
    return {
        "status": "janus-z2-sigma-matter-flux-zero-component-from-transparency-gate",
        "active_core": "Z2_tunnel_Sigma",
        "input_manifest": str(input_path),
        "output_manifest": str(output_path),
        "input_exists": input_exists,
        "upstream_frontiers": {
            "transparency_input_writer": {
                "gate": transparency_writer["status"],
                "passed": transparency_writer["gate_passed"],
                "grid_source_exists": transparency_writer["grid_source_exists"],
                "active_sigma_transparency_derived": transparency_writer[
                    "active_sigma_transparency_derived"
                ],
                "upstream_frontiers": transparency_writer["upstream_frontiers"],
                "nearest_frontier": transparency_writer[
                    "nearest_transparency_input_frontier"
                ],
            },
        },
        "nearest_zero_matter_flux_frontier": {
            "block": "active_Sigma_transparency_input_manifest",
            "gate": "P0EFTJanusZ2SigmaMatterFluxTransparencyInputWriterGate",
            "diagnostic_only": True,
        },
        "input_valid": input_valid,
        "active_sigma_transparency_required": True,
        "matter_flux_zero_without_transparency_forbidden": True,
        "matter_flux_rho_p_values_ready": values_ready,
        "zero_component_output_written": output_written,
        "uses_compressed_planck_lcdm_background": False,
        "uses_archived_z4_inputs": False,
        "uses_phenomenological_holst_bao_scan": False,
        "gate_passed": output_written,
        "validation_error": validation_error,
        "next_required": [
            "supply_outputs_active_z2_sigma_matter_flux_transparency_inputs_json",
            "derive_active_Sigma_transparency_before_zero_flux",
            "merge_zero_matter_flux_components_into_flrw_component_inputs_json",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Matter-Flux Zero Component From Transparency Gate",
        "",
        f"Input exists: `{payload['input_exists']}`",
        f"Input valid: `{payload['input_valid']}`",
        f"Values ready: `{payload['matter_flux_rho_p_values_ready']}`",
        f"Output written: `{payload['zero_component_output_written']}`",
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
