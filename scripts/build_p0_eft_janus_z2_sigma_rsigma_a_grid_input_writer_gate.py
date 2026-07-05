from __future__ import annotations

import json
import sys
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))


SOURCE_PATH = Path("outputs/active_z2_sigma/flrw_component_inputs_without_matter_flux.json")
OUTPUT_PATH = Path("outputs/active_z2_sigma/rsigma_a_grid_inputs.json")
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_rsigma_a_grid_input_writer_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_rsigma_a_grid_input_writer_gate.json")


def _load_grid(path: Path) -> list[float]:
    payload = json.loads(path.read_text(encoding="utf-8"))
    if payload.get("active_core") != "Z2_tunnel_Sigma":
        raise ValueError("grid source active_core must be Z2_tunnel_Sigma")
    if payload.get("source") != "active_derived":
        raise ValueError("grid source must be active_derived")
    for flag in [
        "compressed_planck_lcdm_background_used",
        "archived_z4_background_reuse_used",
        "archived_z4_reuse_used",
        "observational_H0_fit_used",
        "observational_curvature_fit_used",
        "phenomenological_holst_bao_scan_used",
    ]:
        if payload.get(flag, False) is not False:
            raise ValueError(f"Forbidden provenance flag must be false: {flag}")
    grid = np.asarray(payload["a_grid"], dtype=float)
    if grid.ndim != 1 or len(grid) < 2:
        raise ValueError("a_grid must be one-dimensional with at least two points")
    if np.any(grid <= 0.0) or np.any(np.diff(grid) <= 0.0):
        raise ValueError("a_grid must be positive and strictly increasing")
    return grid.tolist()


def build_payload(*, source_path: Path = SOURCE_PATH, output_path: Path = OUTPUT_PATH) -> dict:
    source_exists = source_path.exists()
    output_written = False
    validation_error = None
    if source_exists:
        try:
            a_grid = _load_grid(source_path)
            output_path.parent.mkdir(parents=True, exist_ok=True)
            output_path.write_text(
                json.dumps(
                    {
                        "active_core": "Z2_tunnel_Sigma",
                        "source": "active_derived",
                        "compressed_planck_lcdm_background_used": False,
                        "archived_z4_background_reuse_used": False,
                        "observational_H0_fit_used": False,
                        "observational_curvature_fit_used": False,
                        "phenomenological_holst_bao_scan_used": False,
                        "a_grid": a_grid,
                        "grid_provenance": "active non-matter FLRW component grid",
                    },
                    indent=2,
                ),
                encoding="utf-8",
            )
            output_written = True
        except Exception as exc:
            validation_error = str(exc)
    return {
        "status": "janus-z2-sigma-rsigma-a-grid-input-writer-gate",
        "active_core": "Z2_tunnel_Sigma",
        "source_manifest": str(source_path),
        "output_manifest": str(output_path),
        "source_exists": source_exists,
        "rsigma_a_grid_input_written": output_written,
        "gate_passed": output_written,
        "primary_blocker": "none" if output_written else "active_a_grid_from_non_matter_FLRW_inputs",
        "validation_error": validation_error,
        "next_required": []
        if output_written
        else ["supply_active_flrw_component_inputs_without_matter_flux_json_for_a_grid"],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma R_Sigma a-grid Input Writer Gate",
        "",
        f"Source exists: `{payload['source_exists']}`",
        f"Output written: `{payload['rsigma_a_grid_input_written']}`",
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
