from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from janus_lab.z2_sigma_extrinsic_curvature import build_flrw_extrinsic_curvature_grid_payload
from janus_lab.z2_sigma_flrw_component_manifest import FORBIDDEN_PROVENANCE_TOKENS
from scripts.build_p0_eft_janus_z2_sigma_active_tunnel_embedding_of_a_gate import (
    build_payload as build_active_tunnel_embedding_payload,
)


INPUT_PATH = Path("outputs/active_z2_sigma/flrw_extrinsic_curvature_grid_inputs.json")
OUTPUT_PATH = Path("outputs/active_z2_sigma/flrw_extrinsic_curvature_grid.json")
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_flrw_extrinsic_curvature_grid_writer_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_flrw_extrinsic_curvature_grid_writer_gate.json")


def _load_input(path: Path) -> dict:
    payload = json.loads(path.read_text(encoding="utf-8"))
    if payload.get("active_core") != "Z2_tunnel_Sigma":
        raise ValueError("K-grid input active_core must be Z2_tunnel_Sigma")
    if payload.get("source") != "active_derived":
        raise ValueError("K-grid input source must be active_derived")
    for key in [
        "compressed_planck_lcdm_background_used",
        "archived_z4_reuse_used",
        "phenomenological_holst_bao_scan_used",
    ]:
        if payload.get(key) is not False:
            raise ValueError(f"Forbidden provenance flag must be false: {key}")
    provenance = str(payload.get("K_provenance", "")).strip()
    if not provenance:
        raise ValueError("Missing active provenance for K_provenance")
    if any(token in provenance.lower() for token in FORBIDDEN_PROVENANCE_TOKENS):
        raise ValueError(f"Forbidden provenance for K_provenance: {provenance}")
    return payload


def build_payload(*, input_path: Path = INPUT_PATH, output_path: Path = OUTPUT_PATH) -> dict:
    input_exists = input_path.exists()
    active_embedding = build_active_tunnel_embedding_payload()
    output_written = False
    validation_error = None
    if input_exists:
        try:
            payload = _load_input(input_path)
            built = build_flrw_extrinsic_curvature_grid_payload(
                a_grid=payload["a_grid"],
                k_s_plus=payload["K_s_plus_Z2Sigma"],
                k_s_minus=payload["K_s_minus_Z2Sigma"],
                k_tau_plus=payload["K_tau_plus_Z2Sigma"],
                k_tau_minus=payload["K_tau_minus_Z2Sigma"],
                z2_orientation_sign=payload["z2_orientation_sign"],
                k_provenance=payload["K_provenance"],
            )
            output_path.parent.mkdir(parents=True, exist_ok=True)
            output_path.write_text(json.dumps(built, indent=2), encoding="utf-8")
            output_written = True
        except Exception as exc:
            validation_error = str(exc)
    return {
        "status": "janus-z2-sigma-flrw-extrinsic-curvature-grid-writer-gate",
        "active_core": "Z2_tunnel_Sigma",
        "input_manifest": str(input_path),
        "output_manifest": str(output_path),
        "input_exists": input_exists,
        "active_tunnel_embedding_of_a_closure_ready": active_embedding[
            "active_tunnel_embedding_of_a_closure_ready"
        ],
        "active_tunnel_embedding_derived": active_embedding["derived"],
        "input_active_derived_manifest_is_authoritative": True,
        "flrw_extrinsic_curvature_grid_written": output_written,
        "uses_compressed_planck_lcdm_background": False,
        "uses_archived_z4_inputs": False,
        "uses_phenomenological_holst_bao_scan": False,
        "gate_passed": output_written,
        "validation_error": validation_error,
        "next_required": [
            "run_active_embedding_to_flrw_extrinsic_curvature_input_gate",
            "run_cartan_ghy_deltaK_input_writer_gate",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma FLRW Extrinsic-Curvature Grid Writer Gate",
        "",
        f"Input exists: `{payload['input_exists']}`",
        f"K-grid written: `{payload['flrw_extrinsic_curvature_grid_written']}`",
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
