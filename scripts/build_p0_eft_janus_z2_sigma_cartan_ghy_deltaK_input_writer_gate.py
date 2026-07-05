from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from janus_lab.z2_sigma_cartan_ghy import build_cartan_ghy_deltaK_input_payload


INPUT_PATH = Path("outputs/active_z2_sigma/flrw_extrinsic_curvature_grid.json")
OUTPUT_PATH = Path("outputs/active_z2_sigma/cartan_ghy_deltaK_inputs.json")
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_cartan_ghy_deltaK_input_writer_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_cartan_ghy_deltaK_input_writer_gate.json")


def _load_input(path: Path) -> dict:
    payload = json.loads(path.read_text(encoding="utf-8"))
    if payload.get("active_core") != "Z2_tunnel_Sigma":
        raise ValueError("Extrinsic-curvature grid active_core must be Z2_tunnel_Sigma")
    if payload.get("source") != "active_derived":
        raise ValueError("Extrinsic-curvature grid source must be active_derived")
    for key in [
        "compressed_planck_lcdm_background_used",
        "archived_z4_reuse_used",
        "phenomenological_holst_bao_scan_used",
    ]:
        if payload.get(key) is not False:
            raise ValueError(f"Forbidden provenance flag must be false: {key}")
    return payload


def build_payload(*, input_path: Path = INPUT_PATH, output_path: Path = OUTPUT_PATH) -> dict:
    input_exists = input_path.exists()
    output_written = False
    validation_error = None
    if input_exists:
        try:
            payload = _load_input(input_path)
            built = build_cartan_ghy_deltaK_input_payload(
                a_grid=payload["a_grid"],
                k_s_plus=payload["K_s_plus_Z2Sigma"],
                k_s_minus=payload["K_s_minus_Z2Sigma"],
                k_tau_plus=payload["K_tau_plus_Z2Sigma"],
                k_tau_minus=payload["K_tau_minus_Z2Sigma"],
                z2_orientation_sign=payload["z2_orientation_sign"],
                deltaK_provenance=payload["K_provenance"],
            )
            output_path.parent.mkdir(parents=True, exist_ok=True)
            output_path.write_text(json.dumps(built, indent=2), encoding="utf-8")
            output_written = True
        except Exception as exc:
            validation_error = str(exc)
    return {
        "status": "janus-z2-sigma-cartan-ghy-deltaK-input-writer-gate",
        "active_core": "Z2_tunnel_Sigma",
        "input_manifest": str(input_path),
        "output_manifest": str(output_path),
        "input_exists": input_exists,
        "deltaK_input_written": output_written,
        "uses_compressed_planck_lcdm_background": False,
        "uses_archived_z4_inputs": False,
        "uses_phenomenological_holst_bao_scan": False,
        "gate_passed": output_written,
        "validation_error": validation_error,
        "next_required": [
            "supply_outputs_active_z2_sigma_flrw_extrinsic_curvature_grid_json",
            "run_cartan_ghy_component_from_deltaK_inputs_gate",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Cartan-GHY DeltaK Input Writer Gate",
        "",
        f"Input exists: `{payload['input_exists']}`",
        f"DeltaK input written: `{payload['deltaK_input_written']}`",
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
