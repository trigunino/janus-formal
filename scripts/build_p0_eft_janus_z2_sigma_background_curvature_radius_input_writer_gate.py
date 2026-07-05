from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from janus_lab.z2_sigma_background_inputs import build_active_z2sigma_background_scalar_payload
from scripts.build_p0_eft_janus_z2_sigma_throat_radius_solution_frontier_gate import (
    build_payload as build_throat_radius_frontier_payload,
)


INPUT_PATH = Path("outputs/active_z2_sigma/background_curvature_radius_normalization_inputs.json")
OUTPUT_PATH = Path("outputs/active_z2_sigma/background_curvature_radius_inputs.json")
REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_background_curvature_radius_input_writer_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_background_curvature_radius_input_writer_gate.json"
)


def _normalization_frontier() -> dict:
    frontier = build_throat_radius_frontier_payload()
    return {
        "source_gate": "P0EFTJanusZ2SigmaRSigmaSolutionToEmbeddingCurvatureBranchGate",
        "source_certificate_manifest": "outputs/active_z2_sigma/rsigma_solution_certificate.json",
        "throat_radius_solution_frontier_ready": frontier[
            "throat_radius_solution_certificate_ready"
        ],
        "embedding_unblocked_by_radius_solution": frontier[
            "embedding_unblocked_by_radius_solution"
        ],
        "current_frontier": frontier["current_frontier"],
        "blocks": [
            "matter_flux_radial_block",
            "counterterm_radial_block",
            "solve_E_RSigma_equals_zero_without_fit",
        ],
        "diagnostic_only": True,
    }


def build_payload(*, input_path: Path = INPUT_PATH, output_path: Path = OUTPUT_PATH) -> dict:
    input_exists = input_path.exists()
    output_written = False
    validation_error = None
    radius_value = None
    missing_active_artifact = None if input_exists else str(input_path)
    if input_exists:
        try:
            built = build_active_z2sigma_background_scalar_payload(
                json.loads(input_path.read_text(encoding="utf-8")),
                "R_curv_Z2Sigma_Mpc",
            )
            output_path.parent.mkdir(parents=True, exist_ok=True)
            output_path.write_text(json.dumps(built, indent=2), encoding="utf-8")
            output_written = True
            radius_value = built["scalars"]["R_curv_Z2Sigma_Mpc"]
        except Exception as exc:
            validation_error = str(exc)
    return {
        "status": "janus-z2-sigma-background-curvature-radius-input-writer-gate",
        "active_core": "Z2_tunnel_Sigma",
        "input_manifest": str(input_path),
        "output_manifest": str(output_path),
        "input_exists": input_exists,
        "missing_active_artifact": missing_active_artifact,
        "nearest_missing_artifact": missing_active_artifact,
        "background_curvature_radius_input_written": output_written,
        "R_curv_Z2Sigma_Mpc_value": radius_value,
        "requires_active_curvature_radius_scale_normalization": True,
        "requires_active_embedding_or_throat_radius_scale": True,
        "dimensionless_H0R_over_c_insufficient_for_R_curv": True,
        "normalization_source_frontier": _normalization_frontier(),
        "uses_compressed_planck_lcdm_background": False,
        "uses_archived_z4_background": False,
        "uses_observational_H0_fit": False,
        "uses_observational_curvature_fit": False,
        "gate_passed": output_written,
        "primary_blocker": (
            "none" if output_written else "active_R_curv_scale_normalization_from_RSigma"
        ),
        "validation_error": validation_error,
        "next_required": [
            "derive_active_R_curv_Z2Sigma_Mpc",
            "supply_outputs_active_z2_sigma_background_curvature_radius_normalization_inputs_json",
            "run_background_curvature_branch_inputs_assembler_gate",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Background Curvature Radius Input Writer Gate",
        "",
        f"Input exists: `{payload['input_exists']}`",
        f"Missing active artifact: `{payload['missing_active_artifact']}`",
        f"Radius input written: `{payload['background_curvature_radius_input_written']}`",
        "Scale-free `H0*R_curv/c` alone cannot determine dimensional `R_curv`.",
        f"Gate passed: `{payload['gate_passed']}`",
        "",
        "## Next Required",
    ]
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    if payload["validation_error"]:
        lines.extend(["", "## Validation Error", payload["validation_error"]])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
