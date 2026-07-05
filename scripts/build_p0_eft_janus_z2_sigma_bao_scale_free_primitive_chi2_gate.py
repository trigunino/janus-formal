from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from janus_lab.z2_sigma_active_inputs import load_active_z2sigma_scale_free_bao_inputs
from janus_lab.z2_sigma_active_pipeline import (
    write_scale_free_bao_manifest_from_primitive_manifest,
)
from scripts.build_p0_eft_janus_z2_sigma_bao_scale_free_chi2_gate import (
    build_payload as build_scale_free_chi2_payload,
)


PRIMITIVE_INPUT_PATH = Path("outputs/active_z2_sigma/bao_scale_free_primitive_inputs.json")
SCALE_FREE_INPUT_PATH = Path("outputs/active_z2_sigma/bao_scale_free_inputs.json")
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_bao_scale_free_primitive_chi2_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_bao_scale_free_primitive_chi2_gate.json")


def build_payload(
    primitive_input_path: Path = PRIMITIVE_INPUT_PATH,
    scale_free_input_path: Path = SCALE_FREE_INPUT_PATH,
) -> dict:
    if not primitive_input_path.exists():
        return {
            "status": "janus-z2-sigma-bao-scale-free-primitive-chi2-gate",
            "active_core": "Z2_tunnel_Sigma",
            "primitive_input_manifest": str(primitive_input_path),
            "primitive_input_manifest_available": False,
            "scale_free_bao_input_manifest_written": False,
            "active_scale_free_bao_input_valid": False,
            "scale_free_bao_evaluation": False,
            "bao_chi2_evaluated": False,
            "chi2_DESI_DR2_BAO": None,
            "Gamma_drag_over_H0_Z2Sigma_available": False,
            "uses_compressed_planck_lcdm": False,
            "uses_archived_z4": False,
            "uses_observational_H0_fit": False,
            "gate_passed": False,
            "blocker": "missing active scale-free primitive manifest",
        }

    written = write_scale_free_bao_manifest_from_primitive_manifest(
        primitive_input_path,
        scale_free_input_path,
    )
    try:
        load_active_z2sigma_scale_free_bao_inputs(written)
        active_scale_free_bao_input_valid = True
    except Exception:
        active_scale_free_bao_input_valid = False
    chi2_payload = build_scale_free_chi2_payload(written)
    return {
        "status": "janus-z2-sigma-bao-scale-free-primitive-chi2-gate",
        "active_core": "Z2_tunnel_Sigma",
        "primitive_input_manifest": str(primitive_input_path),
        "primitive_input_manifest_available": True,
        "scale_free_input_manifest": str(written),
        "scale_free_bao_input_manifest_written": True,
        "active_scale_free_bao_input_valid": active_scale_free_bao_input_valid,
        "scale_free_bao_evaluation": chi2_payload["scale_free_bao_evaluation"],
        "bao_chi2_evaluated": chi2_payload["bao_chi2_evaluated"],
        "chi2_DESI_DR2_BAO": chi2_payload.get("chi2_DESI_DR2_BAO"),
        "prediction_vector": chi2_payload.get("prediction_vector"),
        "residual_vector": chi2_payload.get("residual_vector"),
        "rd_hat_Z2Sigma": chi2_payload.get("rd_hat_Z2Sigma"),
        "Gamma_drag_over_H0_Z2Sigma_available": chi2_payload.get(
            "Gamma_drag_over_H0_Z2Sigma_available",
            False,
        ),
        "uses_compressed_planck_lcdm": False,
        "uses_archived_z4": False,
        "uses_observational_H0_fit": False,
        "gate_passed": bool(chi2_payload["bao_scale_free_chi2_gate_passed"]),
        "blocker": None
        if chi2_payload["bao_scale_free_chi2_gate_passed"]
        else chi2_payload.get("blocker", "scale-free chi2 gate blocked"),
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma BAO Scale-Free Primitive Chi2 Gate",
        "",
        f"Primitive manifest: `{payload['primitive_input_manifest']}`",
        f"Primitive manifest available: `{payload['primitive_input_manifest_available']}`",
        f"Scale-free BAO input manifest written: `{payload['scale_free_bao_input_manifest_written']}`",
        f"Scale-free BAO evaluation: `{payload['scale_free_bao_evaluation']}`",
        f"BAO chi2 evaluated: `{payload['bao_chi2_evaluated']}`",
        f"Gamma_drag/H0 available: `{payload['Gamma_drag_over_H0_Z2Sigma_available']}`",
        f"Gate passed: `{payload['gate_passed']}`",
    ]
    if payload["chi2_DESI_DR2_BAO"] is not None:
        lines.append(f"DESI DR2 BAO chi2: `{payload['chi2_DESI_DR2_BAO']}`")
    if payload["blocker"]:
        lines.append(f"Blocker: `{payload['blocker']}`")
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
