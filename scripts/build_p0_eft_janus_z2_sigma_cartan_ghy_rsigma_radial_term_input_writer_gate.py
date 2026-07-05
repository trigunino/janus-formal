from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from janus_lab.z2_sigma_rsigma_radial_terms import (
    build_active_z2sigma_rsigma_radial_term_payload,
    write_active_z2sigma_rsigma_radial_term_manifest,
)


INPUT_PATH = Path("outputs/active_z2_sigma/cartan_ghy_rsigma_radial_term_inputs.json")
OUTPUT_PATH = Path("outputs/active_z2_sigma/rsigma_E_CartanGHY.json")
REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_cartan_ghy_rsigma_radial_term_input_writer_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_cartan_ghy_rsigma_radial_term_input_writer_gate.json"
)


def _load_input(path: Path) -> dict:
    payload = json.loads(path.read_text(encoding="utf-8"))
    if payload.get("active_core") != "Z2_tunnel_Sigma":
        raise ValueError("Input active_core must be Z2_tunnel_Sigma")
    if payload.get("source") != "active_derived":
        raise ValueError("Input source must be active_derived")
    for key in [
        "compressed_planck_lcdm_background_used",
        "archived_z4_background_reuse_used",
        "observational_H0_fit_used",
        "observational_curvature_fit_used",
        "phenomenological_holst_bao_scan_used",
    ]:
        if payload.get(key) is not False:
            raise ValueError(f"Forbidden provenance flag must be false: {key}")
    if payload.get("radial_embedding_variation_evaluated") is not True:
        raise ValueError("radial_embedding_variation_evaluated must be true")
    return payload


def build_payload(*, input_path: Path = INPUT_PATH, output_path: Path = OUTPUT_PATH) -> dict:
    input_exists = input_path.exists()
    output_written = False
    validation_error = None
    if input_exists:
        try:
            source = _load_input(input_path)
            payload = build_active_z2sigma_rsigma_radial_term_payload(
                term_name="E_CartanGHY",
                a_grid=source["a_grid"],
                term_values=source["E_CartanGHY"],
                term_provenance=source["E_CartanGHY_provenance"],
            )
            write_active_z2sigma_rsigma_radial_term_manifest(output_path, payload)
            output_written = True
        except Exception as exc:
            validation_error = str(exc)
    return {
        "status": "janus-z2-sigma-cartan-ghy-rsigma-radial-term-input-writer-gate",
        "active_core": "Z2_tunnel_Sigma",
        "input_manifest": str(input_path),
        "output_manifest": str(output_path),
        "input_exists": input_exists,
        "cartan_ghy_rsigma_radial_term_written": output_written,
        "requires_radial_embedding_variation": True,
        "requires_partial_R_h_and_partial_R_K": True,
        "gate_passed": output_written,
        "primary_blocker": "none" if output_written else "E_CartanGHY_radial_term",
        "validation_error": validation_error,
        "next_required": []
        if output_written
        else [
            "derive_partial_R_h_ab_on_Sigma",
            "derive_partial_R_K_on_Sigma",
            "supply_outputs_active_z2_sigma_cartan_ghy_rsigma_radial_term_inputs_json",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Cartan-GHY R_Sigma Radial Term Writer Gate",
        "",
        f"Input exists: `{payload['input_exists']}`",
        f"Output written: `{payload['cartan_ghy_rsigma_radial_term_written']}`",
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
