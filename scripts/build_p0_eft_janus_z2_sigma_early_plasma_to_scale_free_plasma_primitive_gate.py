from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from janus_lab.z2_sigma_active_inputs import (
    load_active_z2sigma_scale_free_plasma_primitive_inputs,
)
from janus_lab.z2_sigma_active_pipeline import (
    write_scale_free_plasma_primitive_manifest_from_early_plasma_and_h0_manifests,
)
from scripts.build_p0_eft_janus_z2_sigma_background_h0_input_writer_gate import (
    INPUT_PATH as H0_NORMALIZATION_PATH,
)
from scripts.build_p0_eft_janus_z2_sigma_background_h0_input_writer_gate import (
    build_payload as build_h0_payload,
)


EARLY_PLASMA_PATH = Path("outputs/active_z2_sigma/early_plasma.json")
H0_PATH = Path("outputs/active_z2_sigma/background_H0_inputs.json")
PLASMA_PRIMITIVE_PATH = Path("outputs/active_z2_sigma/bao_scale_free_plasma_primitive_inputs.json")
REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_early_plasma_to_scale_free_plasma_primitive_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_early_plasma_to_scale_free_plasma_primitive_gate.json"
)


def build_payload(
    *,
    early_plasma_path: Path = EARLY_PLASMA_PATH,
    h0_normalization_path: Path = H0_NORMALIZATION_PATH,
    h0_path: Path = H0_PATH,
    plasma_primitive_path: Path = PLASMA_PRIMITIVE_PATH,
) -> dict:
    h0_writer = build_h0_payload(input_path=h0_normalization_path, output_path=h0_path)
    input_exists = {
        "early_plasma": early_plasma_path.exists(),
        "active_h0": h0_path.exists(),
    }
    upstream_frontiers = {
        "early_plasma_manifest": {
            "path": str(early_plasma_path),
            "input_exists": input_exists["early_plasma"],
            "required_for": "rho_baryon/rho_photon/Gamma_drag active plasma history",
        },
        "active_h0_manifest": {
            "path": str(h0_path),
            "input_exists": input_exists["active_h0"],
            "upstream_writer": {
                "gate": h0_writer["status"],
                "passed": h0_writer["gate_passed"],
                "input_manifest": h0_writer["input_manifest"],
                "input_exists": h0_writer["input_exists"],
                "nearest_missing_artifact": h0_writer["nearest_missing_artifact"],
                "requires_active_H0_scale_normalization": h0_writer[
                    "requires_active_H0_scale_normalization"
                ],
                "dimensionless_H0R_over_c_insufficient_for_H0": h0_writer[
                    "dimensionless_H0R_over_c_insufficient_for_H0"
                ],
            },
            "required_for": "Gamma_drag_over_H0_Z2Sigma scale-free primitive",
            "observational_H0_fit_forbidden": True,
        },
    }
    missing = [
        name
        for name, frontier in upstream_frontiers.items()
        if not frontier["input_exists"]
    ]
    written = False
    valid = False
    validation_error = None
    z_grid_length = None
    if all(input_exists.values()):
        try:
            path = write_scale_free_plasma_primitive_manifest_from_early_plasma_and_h0_manifests(
                early_plasma_path,
                h0_path,
                plasma_primitive_path,
            )
            written = True
            primitive = load_active_z2sigma_scale_free_plasma_primitive_inputs(path)
            valid = True
            z_grid_length = int(len(primitive.z_grid))
        except Exception as exc:
            validation_error = str(exc)
    return {
        "status": "janus-z2-sigma-early-plasma-to-scale-free-plasma-primitive-gate",
        "active_core": "Z2_tunnel_Sigma",
        "input_manifests": {
            "early_plasma": str(early_plasma_path),
            "active_h0_normalization": str(h0_normalization_path),
            "active_h0": str(h0_path),
        },
        "input_exists": input_exists,
        "upstream_frontiers": upstream_frontiers,
        "nearest_plasma_primitive_frontier": {
            "blocks": missing,
            "diagnostic_only": True,
        },
        "plasma_primitive_manifest": str(plasma_primitive_path),
        "plasma_primitive_written": written,
        "plasma_primitive_valid": valid,
        "z_grid_length": z_grid_length,
        "uses_compressed_planck_lcdm": False,
        "uses_archived_z4": False,
        "uses_observational_H0_fit": False,
        "gate_passed": valid,
        "validation_error": validation_error,
        "blocker": (
            "missing " + ", ".join(missing)
            if missing
            else validation_error
        ),
        "next_required": [
            "supply_outputs_active_z2_sigma_early_plasma_json",
            "supply_outputs_active_z2_sigma_background_H0_inputs_json",
            "merge_background_and_plasma_primitives",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Early Plasma To Scale-Free Plasma Primitive Gate",
        "",
        f"Input exists: `{payload['input_exists']}`",
        f"Plasma primitive written: `{payload['plasma_primitive_written']}`",
        f"Plasma primitive valid: `{payload['plasma_primitive_valid']}`",
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
