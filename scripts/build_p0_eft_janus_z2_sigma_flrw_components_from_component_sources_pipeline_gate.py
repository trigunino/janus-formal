from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z2_sigma_flrw_component_manifest_writer_from_inputs_gate import (
    build_payload as build_manifest_writer_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_flrw_inputs_merge_transparent_matter_flux_gate import (
    build_payload as build_merge_matter_flux_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_flrw_non_matter_inputs_assembler_gate import (
    build_payload as build_non_matter_payload,
)


CARTAN_PATH = Path("outputs/active_z2_sigma/cartan_ghy_components.json")
HOLST_PATH = Path("outputs/active_z2_sigma/holst_nieh_yan_components.json")
COUNTERTERM_PATH = Path("outputs/active_z2_sigma/counterterm_components.json")
MATTER_FLUX_PATH = Path("outputs/active_z2_sigma/matter_flux_zero_components.json")
PARTIAL_INPUT_PATH = Path("outputs/active_z2_sigma/flrw_component_inputs_without_matter_flux.json")
FLRW_INPUT_PATH = Path("outputs/active_z2_sigma/flrw_component_inputs.json")
FLRW_MANIFEST_PATH = Path("outputs/active_z2_sigma/flrw_components.json")
REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_flrw_components_from_component_sources_pipeline_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_flrw_components_from_component_sources_pipeline_gate.json"
)


def build_payload(
    *,
    cartan_path: Path = CARTAN_PATH,
    holst_path: Path = HOLST_PATH,
    counterterm_path: Path = COUNTERTERM_PATH,
    matter_flux_path: Path = MATTER_FLUX_PATH,
    partial_input_path: Path = PARTIAL_INPUT_PATH,
    flrw_input_path: Path = FLRW_INPUT_PATH,
    flrw_manifest_path: Path = FLRW_MANIFEST_PATH,
) -> dict:
    non_matter = build_non_matter_payload(
        cartan_path=cartan_path,
        holst_path=holst_path,
        counterterm_path=counterterm_path,
        output_path=partial_input_path,
    )
    merge = build_merge_matter_flux_payload(
        partial_input_path=partial_input_path,
        matter_flux_path=matter_flux_path,
        output_path=flrw_input_path,
    )
    writer = build_manifest_writer_payload(
        input_path=flrw_input_path,
        manifest_path=flrw_manifest_path,
    )
    gate_passed = (
        non_matter["gate_passed"]
        and merge["gate_passed"]
        and writer["gate_passed"]
    )
    blockers = []
    if not non_matter["gate_passed"]:
        blockers.append("missing Cartan-GHY, Holst/Nieh-Yan, or counterterm components")
    if not merge["gate_passed"]:
        blockers.append("missing transparent matter-flux component")
    if not writer["gate_passed"]:
        blockers.append("FLRW component inputs not ready for manifest writing")
    return {
        "status": "janus-z2-sigma-flrw-components-from-component-sources-pipeline-gate",
        "active_core": "Z2_tunnel_Sigma",
        "non_matter_inputs_passed": non_matter["gate_passed"],
        "transparent_matter_flux_merge_passed": merge["gate_passed"],
        "flrw_component_manifest_writer_passed": writer["gate_passed"],
        "flrw_component_manifest": str(flrw_manifest_path),
        "upstream_frontiers": {
            "non_matter": {
                "gate": non_matter["status"],
                "passed": non_matter["gate_passed"],
                "cartan_ghy_component_exists": non_matter[
                    "cartan_ghy_component_exists"
                ],
                "holst_nieh_yan_component_exists": non_matter[
                    "holst_nieh_yan_component_exists"
                ],
                "counterterm_component_exists": non_matter[
                    "counterterm_component_exists"
                ],
                "upstream_frontiers": non_matter.get("upstream_frontiers", {}),
                "nearest_frontier": non_matter.get("nearest_non_matter_frontier"),
                "validation_error": non_matter["validation_error"],
            },
            "matter_flux_merge": {
                "gate": merge["status"],
                "passed": merge["gate_passed"],
                "partial_input_exists": merge["partial_input_exists"],
                "matter_flux_component_exists": merge["matter_flux_component_exists"],
                "upstream_frontiers": merge.get("upstream_frontiers", {}),
                "nearest_frontier": merge.get("nearest_matter_flux_merge_frontier"),
                "validation_error": merge["validation_error"],
            },
            "manifest_writer": {
                "gate": writer["status"],
                "passed": writer["gate_passed"],
                "input_exists": writer["input_exists"],
                "validation_error": writer["validation_error"],
            },
        },
        "nearest_flrw_components_frontier": {
            "blocks": [
                "Cartan_GHY_components",
                "Holst_Nieh_Yan_components",
                "counterterm_components",
                "transparent_matter_flux_component",
            ],
            "diagnostic_only": True,
        },
        "uses_compressed_planck_lcdm_background": False,
        "uses_archived_z4_inputs": False,
        "uses_phenomenological_holst_bao_scan": False,
        "gate_passed": gate_passed,
        "primary_blocker": "none" if gate_passed else "flrw_component_source_manifests",
        "blocker": None if gate_passed else "; ".join(blockers),
        "next_required": [
            "derive_Cartan_GHY_components",
            "derive_Holst_Nieh_Yan_components",
            "derive_counterterm_components",
            "derive_or_prove_transparent_matter_flux_components",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(
        "\n".join(
            [
                "# Janus Z2/Sigma FLRW Components From Component Sources Pipeline Gate",
                "",
                f"Non-matter inputs passed: `{payload['non_matter_inputs_passed']}`",
                f"Matter-flux merge passed: `{payload['transparent_matter_flux_merge_passed']}`",
                f"Manifest writer passed: `{payload['flrw_component_manifest_writer_passed']}`",
                f"Gate passed: `{payload['gate_passed']}`",
            ]
        ),
        encoding="utf-8",
    )
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
