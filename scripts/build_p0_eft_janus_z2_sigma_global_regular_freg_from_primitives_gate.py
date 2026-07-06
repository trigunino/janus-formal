from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z2_sigma_global_regular_freg_solver_gate import (
    build_payload as build_solver_payload,
)
from src.janus_lab.z2_sigma_global_regularity_primitives import (
    load_and_materialize_freg_components,
)


INPUT_PATH = Path("outputs/active_z2_sigma/global_regular_freg_primitives.json")
COMPONENT_OUTPUT_PATH = Path("outputs/active_z2_sigma/global_regular_freg_components.json")
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_global_regular_freg_from_primitives_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_global_regular_freg_from_primitives_gate.json")


def build_payload(
    *,
    input_path: Path = INPUT_PATH,
    component_output_path: Path = COMPONENT_OUTPUT_PATH,
) -> dict:
    if not input_path.exists():
        return {
            "status": "janus-z2-sigma-global-regular-freg-from-primitives-gate",
            "active_core": "Z2_tunnel_Sigma",
            "primitive_manifest": str(input_path),
            "primitive_manifest_exists": False,
            "component_manifest_written": False,
            "R_Sigma_over_ell_collar_selected": False,
            "full_no_fit_prediction_ready": False,
            "gate_passed": False,
            "primary_blocker": "global_regular_freg_primitives_json",
        }
    validation_error = None
    component_written = False
    solver = None
    try:
        materialized = load_and_materialize_freg_components(input_path)
        component_output_path.parent.mkdir(parents=True, exist_ok=True)
        component_output_path.write_text(
            json.dumps(
                {
                    "active_core": materialized["active_core"],
                    "source": materialized["source"],
                    "compressed_planck_lcdm_used": False,
                    "archived_z4_reuse_used": False,
                    "observational_fit_used": False,
                    "torus_replacement_used": False,
                    "full_no_fit_prediction_ready": False,
                    "lambda_grid": materialized["lambda_grid"],
                    "normal_frame_holonomy_defect": materialized["F_reg_components"][
                        "normal_frame_holonomy_defect"
                    ],
                    "collar_endpoint_mismatch": materialized["F_reg_components"][
                        "collar_endpoint_mismatch"
                    ],
                    "junction_bianchi_defect": materialized["F_reg_components"][
                        "junction_bianchi_defect"
                    ],
                    "root_tolerance": materialized["root_tolerance"],
                    "component_provenance": materialized["component_provenance"],
                },
                indent=2,
            ),
            encoding="utf-8",
        )
        component_written = True
        solver = build_solver_payload(input_path=component_output_path)
    except Exception as exc:
        validation_error = str(exc)
    selected = bool(solver and solver["R_Sigma_over_ell_collar_selected"])
    return {
        "status": "janus-z2-sigma-global-regular-freg-from-primitives-gate",
        "active_core": "Z2_tunnel_Sigma",
        "primitive_manifest": str(input_path),
        "primitive_manifest_exists": True,
        "component_manifest": str(component_output_path),
        "component_manifest_written": component_written,
        "R_Sigma_over_ell_collar_selected": selected,
        "regularity_roots": [] if solver is None else solver["regularity_roots"],
        "full_no_fit_prediction_ready": False,
        "gate_passed": selected,
        "primary_blocker": "none" if selected else "unique_global_regular_root_not_found",
        "validation_error": validation_error,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Global Regular F_reg From Primitives Gate",
        "",
        f"Primitive manifest exists: `{payload['primitive_manifest_exists']}`",
        f"Component manifest written: `{payload['component_manifest_written']}`",
        f"Ratio selected: `{payload['R_Sigma_over_ell_collar_selected']}`",
        f"Full no-fit prediction ready: `{payload['full_no_fit_prediction_ready']}`",
    ]
    if payload.get("validation_error"):
        lines.extend(["", "## Validation Error", payload["validation_error"]])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
