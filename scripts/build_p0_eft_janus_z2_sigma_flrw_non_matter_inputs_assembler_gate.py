from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from janus_lab.z2_sigma_flrw_component_inputs import (
    merge_active_non_matter_flrw_component_payloads,
)


CARTAN_PATH = Path("outputs/active_z2_sigma/cartan_ghy_components.json")
HOLST_PATH = Path("outputs/active_z2_sigma/holst_nieh_yan_components.json")
COUNTERTERM_PATH = Path("outputs/active_z2_sigma/counterterm_components.json")
OUTPUT_PATH = Path("outputs/active_z2_sigma/flrw_component_inputs_without_matter_flux.json")
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_flrw_non_matter_inputs_assembler_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_flrw_non_matter_inputs_assembler_gate.json")

CARTAN_DELTAK_INPUT_PATH = Path("outputs/active_z2_sigma/cartan_ghy_deltaK_inputs.json")
BACKGROUND_SCALAR_PATH = Path("outputs/active_z2_sigma/background_scalars.json")
HOLST_INPUT_PATH = Path("outputs/active_z2_sigma/holst_nieh_yan_component_inputs.json")
COUNTERTERM_INPUT_PATH = Path("outputs/active_z2_sigma/counterterm_component_inputs.json")


def _read_json(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def _component_frontiers(
    *,
    cartan_path: Path,
    holst_path: Path,
    counterterm_path: Path,
) -> dict:
    return {
        "cartan_ghy_component": {
            "gate": "janus-z2-sigma-cartan-ghy-component-from-deltaK-inputs-gate",
            "component_manifest": str(cartan_path),
            "component_exists": cartan_path.exists(),
            "required_inputs": [
                {
                    "path": str(CARTAN_DELTAK_INPUT_PATH),
                    "exists": CARTAN_DELTAK_INPUT_PATH.exists(),
                    "gate": "janus-z2-sigma-cartan-ghy-deltaK-input-writer-gate",
                },
                {
                    "path": str(BACKGROUND_SCALAR_PATH),
                    "exists": BACKGROUND_SCALAR_PATH.exists(),
                    "gate": "janus-z2-sigma-background-scalar-manifest-writer-from-inputs-gate",
                },
            ],
            "next_required": [
                "supply_active_DeltaK_s_and_DeltaK_tau_inputs",
                "supply_active_kappa_rho_crit0_background_scalars",
            ],
            "diagnostic_only": True,
        },
        "holst_nieh_yan_component": {
            "gate": "janus-z2-sigma-holst-nieh-yan-component-from-inputs-gate",
            "component_manifest": str(holst_path),
            "component_exists": holst_path.exists(),
            "required_inputs": [
                {
                    "path": str(HOLST_INPUT_PATH),
                    "exists": HOLST_INPUT_PATH.exists(),
                    "gate": "janus-z2-sigma-holst-nieh-yan-component-from-inputs-gate",
                }
            ],
            "next_required": [
                "derive_Holst_Nieh_Yan_FLRW_stress_reduction",
                "write_active_holst_nieh_yan_component_inputs",
            ],
            "diagnostic_only": True,
        },
        "counterterm_component": {
            "gate": "janus-z2-sigma-counterterm-component-from-inputs-gate",
            "component_manifest": str(counterterm_path),
            "component_exists": counterterm_path.exists(),
            "required_inputs": [
                {
                    "path": str(COUNTERTERM_INPUT_PATH),
                    "exists": COUNTERTERM_INPUT_PATH.exists(),
                    "gate": "janus-z2-sigma-counterterm-component-from-inputs-gate",
                }
            ],
            "next_required": [
                "derive_counterterm_FLRW_stress_reduction",
                "derive_counterterm_radial_reduction",
                "write_active_counterterm_component_inputs",
            ],
            "diagnostic_only": True,
        },
    }


def build_payload(
    *,
    cartan_path: Path = CARTAN_PATH,
    holst_path: Path = HOLST_PATH,
    counterterm_path: Path = COUNTERTERM_PATH,
    output_path: Path = OUTPUT_PATH,
) -> dict:
    cartan_exists = cartan_path.exists()
    holst_exists = holst_path.exists()
    counterterm_exists = counterterm_path.exists()
    upstream_frontiers = _component_frontiers(
        cartan_path=cartan_path,
        holst_path=holst_path,
        counterterm_path=counterterm_path,
    )
    missing_components = [
        key
        for key, frontier in upstream_frontiers.items()
        if not frontier["component_exists"]
    ]
    output_written = False
    validation_error = None
    if cartan_exists and holst_exists and counterterm_exists:
        try:
            merged = merge_active_non_matter_flrw_component_payloads(
                cartan_ghy_payload=_read_json(cartan_path),
                holst_nieh_yan_payload=_read_json(holst_path),
                counterterm_payload=_read_json(counterterm_path),
            )
            output_path.parent.mkdir(parents=True, exist_ok=True)
            output_path.write_text(json.dumps(merged, indent=2), encoding="utf-8")
            output_written = True
        except Exception as exc:
            validation_error = str(exc)
    return {
        "status": "janus-z2-sigma-flrw-non-matter-inputs-assembler-gate",
        "active_core": "Z2_tunnel_Sigma",
        "cartan_ghy_component_manifest": str(cartan_path),
        "holst_nieh_yan_component_manifest": str(holst_path),
        "counterterm_component_manifest": str(counterterm_path),
        "output_manifest": str(output_path),
        "cartan_ghy_component_exists": cartan_exists,
        "holst_nieh_yan_component_exists": holst_exists,
        "counterterm_component_exists": counterterm_exists,
        "upstream_frontiers": upstream_frontiers,
        "nearest_non_matter_frontier": {
            "blocks": missing_components,
            "diagnostic_only": True,
        },
        "non_matter_flrw_inputs_written": output_written,
        "uses_compressed_planck_lcdm_background": False,
        "uses_archived_z4_inputs": False,
        "uses_phenomenological_holst_bao_scan": False,
        "gate_passed": output_written,
        "primary_blocker": "none" if output_written else "cartan_holst_counterterm_components",
        "validation_error": validation_error,
        "next_required": [
            "pass_Cartan_GHY_component_from_deltaK_inputs_gate",
            "derive_and_write_Holst_Nieh_Yan_components",
            "derive_and_write_counterterm_components",
            "run_flrw_inputs_merge_transparent_matter_flux_gate",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma FLRW Non-Matter Inputs Assembler Gate",
        "",
        f"Cartan component exists: `{payload['cartan_ghy_component_exists']}`",
        f"Holst component exists: `{payload['holst_nieh_yan_component_exists']}`",
        f"Counterterm component exists: `{payload['counterterm_component_exists']}`",
        f"Non-matter FLRW input written: `{payload['non_matter_flrw_inputs_written']}`",
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
