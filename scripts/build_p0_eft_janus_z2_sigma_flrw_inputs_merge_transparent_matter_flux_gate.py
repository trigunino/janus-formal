from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from janus_lab.z2_sigma_flrw_component_inputs import (
    load_active_z2sigma_flrw_component_input_manifest,
    merge_active_flrw_components_with_matter_flux,
)
from scripts.build_p0_eft_janus_z2_sigma_matter_flux_zero_component_from_transparency_gate import (
    build_payload as build_zero_matter_flux_payload,
)


PARTIAL_INPUT_PATH = Path("outputs/active_z2_sigma/flrw_component_inputs_without_matter_flux.json")
MATTER_FLUX_PATH = Path("outputs/active_z2_sigma/matter_flux_zero_components.json")
OUTPUT_PATH = Path("outputs/active_z2_sigma/flrw_component_inputs.json")
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_flrw_inputs_merge_transparent_matter_flux_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_flrw_inputs_merge_transparent_matter_flux_gate.json")


def build_payload(
    *,
    partial_input_path: Path = PARTIAL_INPUT_PATH,
    matter_flux_path: Path = MATTER_FLUX_PATH,
    output_path: Path = OUTPUT_PATH,
) -> dict:
    zero_matter_flux = build_zero_matter_flux_payload(output_path=matter_flux_path)
    partial_exists = partial_input_path.exists()
    matter_flux_exists = matter_flux_path.exists()
    merged_input_written = False
    validation_error = None
    if partial_exists and matter_flux_exists:
        try:
            partial_payload = json.loads(partial_input_path.read_text(encoding="utf-8"))
            matter_flux_payload = json.loads(matter_flux_path.read_text(encoding="utf-8"))
            merged = merge_active_flrw_components_with_matter_flux(
                partial_payload,
                matter_flux_payload,
            )
            output_path.parent.mkdir(parents=True, exist_ok=True)
            output_path.write_text(json.dumps(merged, indent=2), encoding="utf-8")
            load_active_z2sigma_flrw_component_input_manifest(output_path)
            merged_input_written = True
        except Exception as exc:
            validation_error = str(exc)
    return {
        "status": "janus-z2-sigma-flrw-inputs-merge-transparent-matter-flux-gate",
        "active_core": "Z2_tunnel_Sigma",
        "partial_input_manifest": str(partial_input_path),
        "matter_flux_component_manifest": str(matter_flux_path),
        "output_manifest": str(output_path),
        "partial_input_exists": partial_exists,
        "matter_flux_component_exists": matter_flux_exists,
        "upstream_frontiers": {
            "zero_matter_flux_component": {
                "gate": zero_matter_flux["status"],
                "passed": zero_matter_flux["gate_passed"],
                "input_exists": zero_matter_flux["input_exists"],
                "upstream_frontiers": zero_matter_flux["upstream_frontiers"],
                "nearest_frontier": zero_matter_flux["nearest_zero_matter_flux_frontier"],
            },
        },
        "nearest_matter_flux_merge_frontier": {
            "blocks": [
                "non_matter_FLRW_partial_inputs",
                "zero_matter_flux_component_from_Sigma_transparency",
            ],
            "diagnostic_only": True,
        },
        "requires_active_sigma_transparency_derived": True,
        "merged_flrw_component_inputs_written": merged_input_written,
        "uses_compressed_planck_lcdm_background": False,
        "uses_archived_z4_inputs": False,
        "uses_phenomenological_holst_bao_scan": False,
        "gate_passed": merged_input_written,
        "primary_blocker": (
            "none" if merged_input_written else "non_matter_inputs_and_transparent_matter_flux"
        ),
        "validation_error": validation_error,
        "next_required": [
            "supply_active_flrw_component_inputs_without_matter_flux_json",
            "pass_matter_flux_zero_component_from_transparency_gate",
            "run_flrw_component_manifest_writer_from_inputs_gate",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma FLRW Inputs Merge Transparent Matter-Flux Gate",
        "",
        f"Partial input exists: `{payload['partial_input_exists']}`",
        f"Matter-flux component exists: `{payload['matter_flux_component_exists']}`",
        f"Merged input written: `{payload['merged_flrw_component_inputs_written']}`",
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
