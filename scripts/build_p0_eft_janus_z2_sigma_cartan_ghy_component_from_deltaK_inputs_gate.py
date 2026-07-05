from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from janus_lab.z2_sigma_background_manifest import load_active_z2sigma_background_scalar_manifest
from janus_lab.z2_sigma_cartan_ghy import build_cartan_ghy_component_payload


DELTAK_INPUT_PATH = Path("outputs/active_z2_sigma/cartan_ghy_deltaK_inputs.json")
BACKGROUND_SCALAR_PATH = Path("outputs/active_z2_sigma/background_scalars.json")
OUTPUT_PATH = Path("outputs/active_z2_sigma/cartan_ghy_components.json")
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_cartan_ghy_component_from_deltaK_inputs_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_cartan_ghy_component_from_deltaK_inputs_gate.json")


def _load_deltaK_inputs(path: Path) -> dict:
    payload = json.loads(path.read_text(encoding="utf-8"))
    if payload.get("active_core") != "Z2_tunnel_Sigma":
        raise ValueError("DeltaK input active_core must be Z2_tunnel_Sigma")
    if payload.get("source") != "active_derived":
        raise ValueError("DeltaK input source must be active_derived")
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
    deltaK_input_path: Path = DELTAK_INPUT_PATH,
    background_scalar_path: Path = BACKGROUND_SCALAR_PATH,
    output_path: Path = OUTPUT_PATH,
) -> dict:
    deltaK_exists = deltaK_input_path.exists()
    background_exists = background_scalar_path.exists()
    output_written = False
    validation_error = None
    missing_inputs = []
    if not deltaK_exists:
        missing_inputs.append("active_DeltaK_s_tau_inputs")
    if not background_exists:
        missing_inputs.append("active_background_scalars_kappa_rho_crit0")
    if deltaK_exists and background_exists:
        try:
            deltaK_payload = _load_deltaK_inputs(deltaK_input_path)
            background_payload = load_active_z2sigma_background_scalar_manifest(background_scalar_path)
            component_payload = build_cartan_ghy_component_payload(
                a_grid=deltaK_payload["a_grid"],
                delta_k_s=deltaK_payload["DeltaK_s_Z2Sigma"],
                delta_k_tau=deltaK_payload["DeltaK_tau_Z2Sigma"],
                z2_orientation_sign=deltaK_payload["z2_orientation_sign"],
                kappa_rho_crit0=background_payload["critical_normalization"][
                    "kappa_rho_crit0_Z2Sigma_SI"
                ],
                component_provenance=deltaK_payload["DeltaK_provenance"],
            )
            output_path.parent.mkdir(parents=True, exist_ok=True)
            output_path.write_text(json.dumps(component_payload, indent=2), encoding="utf-8")
            output_written = True
        except Exception as exc:
            validation_error = str(exc)
    return {
        "status": "janus-z2-sigma-cartan-ghy-component-from-deltaK-inputs-gate",
        "active_core": "Z2_tunnel_Sigma",
        "deltaK_input_manifest": str(deltaK_input_path),
        "background_scalar_manifest": str(background_scalar_path),
        "output_manifest": str(output_path),
        "deltaK_input_exists": deltaK_exists,
        "background_scalar_manifest_exists": background_exists,
        "upstream_frontiers": {
            "deltaK_input_writer": {
                "gate": "janus-z2-sigma-cartan-ghy-deltaK-input-writer-gate",
                "path": str(deltaK_input_path),
                "input_exists": deltaK_exists,
                "required_for": "DeltaK_s/tau(a) jump input for Cartan-GHY FLRW component",
            },
            "background_scalar_manifest": {
                "gate": "janus-z2-sigma-background-scalar-manifest-writer-from-inputs-gate",
                "path": str(background_scalar_path),
                "input_exists": background_exists,
                "required_for": "kappa*rho_crit0 normalization for Cartan-GHY component",
            },
        },
        "nearest_cartan_component_frontier": {
            "blocks": missing_inputs,
            "diagnostic_only": True,
        },
        "requires_active_DeltaK_s_of_a": True,
        "requires_active_DeltaK_tau_of_a": True,
        "requires_active_kappa_rho_crit0": True,
        "cartan_ghy_component_values_ready": output_written,
        "cartan_ghy_component_output_written": output_written,
        "uses_compressed_planck_lcdm_background": False,
        "uses_archived_z4_inputs": False,
        "uses_phenomenological_holst_bao_scan": False,
        "gate_passed": output_written,
        "validation_error": validation_error,
        "next_required": [
            "supply_outputs_active_z2_sigma_cartan_ghy_deltaK_inputs_json",
            "supply_outputs_active_z2_sigma_background_scalars_json",
            "merge_Cartan_GHY_components_into_flrw_component_inputs_without_matter_flux",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Cartan-GHY Component From DeltaK Inputs Gate",
        "",
        f"DeltaK input exists: `{payload['deltaK_input_exists']}`",
        f"Background scalar manifest exists: `{payload['background_scalar_manifest_exists']}`",
        f"Component output written: `{payload['cartan_ghy_component_output_written']}`",
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
