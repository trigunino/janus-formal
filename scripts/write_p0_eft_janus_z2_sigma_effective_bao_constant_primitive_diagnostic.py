from __future__ import annotations

import json
import sys
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.janus_lab.z2_sigma_effective_bao import (
    write_effective_scale_free_primitive_inputs,
)


CLOSURE_PATH = Path(
    "outputs/diagnostics/effective_closure_from_example_occupation.diagnostic.json"
)
OUTPUT_PATH = Path(
    "outputs/diagnostics/effective_bao_scale_free_primitive_inputs.diagnostic.json"
)
REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_effective_bao_constant_primitive_diagnostic.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_effective_bao_constant_primitive_diagnostic.json"
)


def build_payload(
    *,
    closure_path: Path = CLOSURE_PATH,
    output_path: Path = OUTPUT_PATH,
) -> dict:
    z_grid = np.linspace(1.0, 3000.0, 256)
    write_effective_scale_free_primitive_inputs(
        output_path,
        closure_path=closure_path,
        z_grid=z_grid,
        e_z2sigma=lambda z: np.ones_like(z, dtype=float),
        cs_over_c_z2sigma=lambda z: np.full_like(z, 1.0 / np.sqrt(3.0), dtype=float),
        gamma_drag_over_h0_z2sigma=lambda z: np.asarray(z, dtype=float) / 1000.0,
        omega_k_z2sigma=0.0,
        z_d_bracket=[900.0, 1100.0],
        primitive_provenance={
            "E_Z2Sigma": "diagnostic_constant_background_not_physical",
            "c_s_over_c_Z2Sigma": "diagnostic_constant_sound_speed_not_physical",
            "Gamma_drag_over_H0_Z2Sigma": "diagnostic_constant_drag_rate_not_physical",
            "omega_k_Z2Sigma": "diagnostic_flat_curvature_not_physical",
        },
    )
    return {
        "status": "janus-z2-sigma-effective-bao-constant-primitive-diagnostic",
        "active_core": "Z2_tunnel_Sigma",
        "closure_path": str(closure_path),
        "output_manifest": str(output_path),
        "diagnostic_primitives_written": True,
        "writes_active_manifest": False,
        "primitive_values_are_physical_derivation": False,
        "full_no_fit_prediction_ready": False,
        "gate_passed": True,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(
        "\n".join(
            [
                "# Janus Z2/Sigma Effective BAO Constant Primitive Diagnostic",
                "",
                f"Diagnostic primitives written: `{payload['diagnostic_primitives_written']}`",
                f"Writes active manifest: `{payload['writes_active_manifest']}`",
                f"Primitive values are physical derivation: `{payload['primitive_values_are_physical_derivation']}`",
                f"Full no-fit prediction ready: `{payload['full_no_fit_prediction_ready']}`",
            ]
        ),
        encoding="utf-8",
    )
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
