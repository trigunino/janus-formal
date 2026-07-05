from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from janus_lab.z2_sigma_flrw_component_inputs import build_active_flrw_component_pair_payload


INPUT_PATH = Path("outputs/active_z2_sigma/counterterm_component_inputs.json")
OUTPUT_PATH = Path("outputs/active_z2_sigma/counterterm_components.json")
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_counterterm_component_from_inputs_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_counterterm_component_from_inputs_gate.json")


def _load_input(path: Path) -> dict:
    payload = json.loads(path.read_text(encoding="utf-8"))
    if payload.get("active_core") != "Z2_tunnel_Sigma":
        raise ValueError("Input active_core must be Z2_tunnel_Sigma")
    if payload.get("source") != "active_derived":
        raise ValueError("Input source must be active_derived")
    for key in [
        "compressed_planck_lcdm_background_used",
        "archived_z4_reuse_used",
        "phenomenological_holst_bao_scan_used",
        "fitted_counterterm_coefficient_used",
    ]:
        if payload.get(key) is not False:
            raise ValueError(f"Forbidden provenance flag must be false: {key}")
    if payload.get("counterterm_FLRW_stress_reduced") is not True:
        raise ValueError("counterterm_FLRW_stress_reduced must be true")
    if payload.get("counterterm_radial_reduction_ready") is not True:
        raise ValueError("counterterm_radial_reduction_ready must be true")
    return payload


def build_payload(*, input_path: Path = INPUT_PATH, output_path: Path = OUTPUT_PATH) -> dict:
    input_exists = input_path.exists()
    output_written = False
    validation_error = None
    if input_exists:
        try:
            source = _load_input(input_path)
            component = build_active_flrw_component_pair_payload(
                a_grid=source["a_grid"],
                rho_field="counterterm_rho",
                pressure_field="counterterm_p",
                rho_values=source["counterterm_rho"],
                pressure_values=source["counterterm_p"],
                component_route="counterterm_from_active_flrw_reduction",
                component_provenance=source["counterterm_provenance"],
            )
            output_path.parent.mkdir(parents=True, exist_ok=True)
            output_path.write_text(json.dumps(component, indent=2), encoding="utf-8")
            output_written = True
        except Exception as exc:
            validation_error = str(exc)
    return {
        "status": "janus-z2-sigma-counterterm-component-from-inputs-gate",
        "active_core": "Z2_tunnel_Sigma",
        "input_manifest": str(input_path),
        "output_manifest": str(output_path),
        "input_exists": input_exists,
        "requires_active_counterterm_FLRW_reduction": True,
        "counterterm_component_values_ready": output_written,
        "counterterm_component_output_written": output_written,
        "uses_compressed_planck_lcdm_background": False,
        "uses_archived_z4_inputs": False,
        "uses_phenomenological_holst_bao_scan": False,
        "requires_counterterm_FLRW_stress_reduced": True,
        "requires_counterterm_radial_reduction_ready": True,
        "gate_passed": output_written,
        "validation_error": validation_error,
        "next_required": [
            "derive_counterterm_FLRW_stress_reduction",
            "supply_outputs_active_z2_sigma_counterterm_component_inputs_json",
            "run_flrw_non_matter_inputs_assembler_gate",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Counterterm Component From Inputs Gate",
        "",
        f"Input exists: `{payload['input_exists']}`",
        f"Component output written: `{payload['counterterm_component_output_written']}`",
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
