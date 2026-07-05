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


INPUT_PATH = Path("outputs/active_z2_sigma/matter_flux_transparency_inputs.json")
OUTPUT_PATH = Path("outputs/active_z2_sigma/rsigma_E_matterFlux.json")
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_rsigma_matter_flux_radial_term_from_transparency_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_rsigma_matter_flux_radial_term_from_transparency_gate.json")


def _load_input(path: Path) -> dict:
    payload = json.loads(path.read_text(encoding="utf-8"))
    if payload.get("active_core") != "Z2_tunnel_Sigma":
        raise ValueError("transparency active_core must be Z2_tunnel_Sigma")
    if payload.get("source") != "active_derived":
        raise ValueError("transparency source must be active_derived")
    for key in [
        "compressed_planck_lcdm_background_used",
        "archived_z4_reuse_used",
        "archived_z4_background_reuse_used",
        "phenomenological_holst_bao_scan_used",
    ]:
        if payload.get(key, False) is not False:
            raise ValueError(f"Forbidden provenance flag must be false: {key}")
    if payload.get("active_sigma_transparency_derived") is not True:
        raise ValueError("active_sigma_transparency_derived must be true")
    return payload


def build_payload(*, input_path: Path = INPUT_PATH, output_path: Path = OUTPUT_PATH) -> dict:
    input_exists = input_path.exists()
    output_written = False
    validation_error = None
    if input_exists:
        try:
            source = _load_input(input_path)
            a_grid = list(source["a_grid"])
            term = build_active_z2sigma_rsigma_radial_term_payload(
                term_name="E_matterFlux",
                a_grid=a_grid,
                term_values=[0.0 for _ in a_grid],
                term_provenance=(
                    "active Sigma transparency: no normal matter flux contribution to R_Sigma"
                ),
            )
            write_active_z2sigma_rsigma_radial_term_manifest(output_path, term)
            output_written = True
        except Exception as exc:
            validation_error = str(exc)
    return {
        "status": "janus-z2-sigma-rsigma-matter-flux-radial-term-from-transparency-gate",
        "active_core": "Z2_tunnel_Sigma",
        "input_manifest": str(input_path),
        "output_manifest": str(output_path),
        "input_exists": input_exists,
        "E_matterFlux_zero_from_transparency_written": output_written,
        "gate_passed": output_written,
        "primary_blocker": "none" if output_written else "active_Sigma_transparency_manifest",
        "validation_error": validation_error,
        "next_required": []
        if output_written
        else [
            "derive_active_Sigma_transparency",
            "write_outputs_active_z2_sigma_matter_flux_transparency_inputs_json",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma R_Sigma Matter-Flux Radial Term From Transparency Gate",
        "",
        f"Output written: `{payload['E_matterFlux_zero_from_transparency_written']}`",
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
