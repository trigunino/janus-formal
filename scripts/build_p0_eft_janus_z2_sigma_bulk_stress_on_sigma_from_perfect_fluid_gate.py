from __future__ import annotations

import json
import sys
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from janus_lab.z2_sigma_matter_flux import build_bulk_stress_on_sigma_payload


INPUT_PATH = Path("outputs/active_z2_sigma/sector_perfect_fluid_on_sigma_inputs.json")
OUTPUT_PATH = Path("outputs/active_z2_sigma/bulk_stress_on_sigma_inputs.json")
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_bulk_stress_on_sigma_from_perfect_fluid_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_bulk_stress_on_sigma_from_perfect_fluid_gate.json")

FORBIDDEN_FLAGS = [
    "compressed_planck_lcdm_background_used",
    "archived_z4_reuse_used",
    "archived_z4_background_reuse_used",
    "phenomenological_holst_bao_scan_used",
    "observational_H0_fit_used",
    "observational_curvature_fit_used",
]


def _load_input(path: Path) -> dict:
    payload = json.loads(path.read_text(encoding="utf-8"))
    if payload.get("active_core") != "Z2_tunnel_Sigma":
        raise ValueError("perfect-fluid input active_core must be Z2_tunnel_Sigma")
    if payload.get("source") != "active_derived":
        raise ValueError("perfect-fluid input source must be active_derived")
    for key in FORBIDDEN_FLAGS:
        if payload.get(key, False) is not False:
            raise ValueError(f"Forbidden provenance flag must be false: {key}")
    if payload.get("sector_perfect_fluid_on_sigma_ready") is not True:
        raise ValueError("sector_perfect_fluid_on_sigma_ready must be true")
    grid = np.asarray(payload["a_grid"], dtype=float)
    if grid.ndim != 1 or len(grid) < 2 or np.any(grid <= 0.0) or np.any(np.diff(grid) <= 0.0):
        raise ValueError("a_grid must be positive and strictly increasing")
    for key in [
        "rho_plus_values",
        "p_plus_values",
        "metric_plus_munu_values",
        "u_plus_contravariant_values",
        "rho_minus_values",
        "p_minus_values",
        "metric_minus_munu_values",
        "u_minus_contravariant_values",
    ]:
        if key not in payload:
            raise ValueError(f"perfect-fluid input missing {key}")
    return payload


def build_payload(
    *,
    input_path: Path = INPUT_PATH,
    output_path: Path = OUTPUT_PATH,
) -> dict:
    input_exists = input_path.exists()
    output_written = False
    validation_error = None
    if input_exists:
        try:
            output = build_bulk_stress_on_sigma_payload(_load_input(input_path))
            output_path.parent.mkdir(parents=True, exist_ok=True)
            output_path.write_text(json.dumps(output, indent=2), encoding="utf-8")
            output_written = True
        except Exception as exc:
            validation_error = str(exc)
    return {
        "status": "janus-z2-sigma-bulk-stress-on-sigma-from-perfect-fluid-gate",
        "active_core": "Z2_tunnel_Sigma",
        "input_manifest": str(input_path),
        "output_manifest": str(output_path),
        "input_exists": input_exists,
        "bulk_stress_on_sigma_written": output_written,
        "gate_passed": output_written,
        "primary_blocker": "none" if output_written else "sector_perfect_fluid_on_sigma_inputs",
        "validation_error": validation_error,
        "next_required": []
        if output_written
        else [
            "derive_sector_rho_p_on_Sigma",
            "derive_metric_plus_minus_on_Sigma",
            "derive_four_velocity_plus_minus_on_Sigma",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Bulk Stress On Sigma From Perfect Fluid Gate",
        "",
        f"Output written: `{payload['bulk_stress_on_sigma_written']}`",
        f"Gate passed: `{payload['gate_passed']}`",
        f"Primary blocker: `{payload['primary_blocker']}`",
    ]
    if payload["validation_error"]:
        lines.extend(["", "## Validation Error", payload["validation_error"]])
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
