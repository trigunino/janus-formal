from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))


INPUT_PATH = Path("outputs/active_z2_sigma/counterterm_minimal_basis_coefficients.json")
OUTPUT_PATH = Path("outputs/active_z2_sigma/surface_hk_active_density_coefficients.json")
REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_surface_hk_coefficients_from_minimal_counterterm.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_surface_hk_coefficients_from_minimal_counterterm.json"
)


def _load_active(path: Path) -> dict:
    payload = json.loads(path.read_text(encoding="utf-8"))
    if payload.get("active_core") != "Z2_tunnel_Sigma":
        raise ValueError("minimal coefficient active_core must be Z2_tunnel_Sigma")
    if payload.get("source") != "active_derived":
        raise ValueError("minimal coefficient source must be active_derived")
    for key in [
        "compressed_planck_lcdm_background_used",
        "archived_z4_reuse_used",
        "archived_z4_background_reuse_used",
        "phenomenological_holst_bao_scan_used",
        "observational_H0_fit_used",
        "observational_curvature_fit_used",
        "fitted_counterterm_coefficient_used",
    ]:
        if payload.get(key, False) is not False:
            raise ValueError(f"forbidden provenance flag must be false: {key}")
    return payload


def _build(source: dict) -> dict:
    for key in ["a_grid", "c1_values", "c2_values", "c3_values"]:
        if key not in source:
            raise ValueError(f"minimal coefficient payload missing {key}")
    a_grid = source["a_grid"]
    n = len(a_grid)
    for key in ["c1_values", "c2_values", "c3_values"]:
        if len(source[key]) != n:
            raise ValueError(f"{key} must align with a_grid")
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_reuse_used": False,
        "archived_z4_background_reuse_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "observational_H0_fit_used": False,
        "observational_curvature_fit_used": False,
        "fitted_counterterm_coefficient_used": False,
        "a_grid": a_grid,
        "a0_values": [0.0 for _ in a_grid],
        "a1_values": source["c1_values"],
        "a2_values": source["c2_values"],
        "a3_values": source["c3_values"],
        "coefficient_source": "counterterm_minimal_basis_coefficients",
        "coefficient_status": source.get("coefficient_status", "unknown"),
        "a0_status": "zero_not_derived_tension_channel_absent_in_minimal_counterterm_basis",
        "active_density_coefficients_ready": True,
        "full_surface_density_derived": False,
        "diagnostic_only": True,
        "forbidden_promotion_reason": (
            "a0/tension channel is not derived by the minimal counterterm trace basis"
        ),
    }


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
            output = _build(_load_active(input_path))
            output_path.parent.mkdir(parents=True, exist_ok=True)
            output_path.write_text(json.dumps(output, indent=2), encoding="utf-8")
            output_written = True
        except Exception as exc:
            validation_error = str(exc)
    return {
        "status": "janus-z2-sigma-surface-hk-coefficients-from-minimal-counterterm",
        "active_core": "Z2_tunnel_Sigma",
        "input_manifest": str(input_path),
        "output_manifest": str(output_path),
        "input_exists": input_exists,
        "surface_hk_coefficients_written": output_written,
        "gate_passed": output_written,
        "diagnostic_only": output_written,
        "primary_blocker": "none" if output_written else "counterterm_minimal_basis_coefficients",
        "validation_error": validation_error,
        "next_required": []
        if output_written
        else [
            "derive_counterterm_trace_residual_inputs",
            "run_counterterm_minimal_basis_coefficient_solver",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Surface h/K Coefficients From Minimal Counterterm",
        "",
        f"Output written: `{payload['surface_hk_coefficients_written']}`",
        f"Diagnostic only: `{payload['diagnostic_only']}`",
        f"Primary blocker: `{payload['primary_blocker']}`",
    ]
    if payload["validation_error"]:
        lines.extend(["", "## Validation Error", payload["validation_error"]])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
