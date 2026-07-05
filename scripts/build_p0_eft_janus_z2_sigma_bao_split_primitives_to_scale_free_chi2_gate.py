from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z2_sigma_bao_scale_free_primitive_chi2_gate import (
    build_payload as build_primitive_chi2_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_bao_scale_free_primitive_inputs_assembler_gate import (
    build_payload as build_primitive_assembler_payload,
)


BACKGROUND_PRIMITIVE_PATH = Path("outputs/active_z2_sigma/bao_scale_free_background_primitive_inputs.json")
PLASMA_PRIMITIVE_PATH = Path("outputs/active_z2_sigma/bao_scale_free_plasma_primitive_inputs.json")
PRIMITIVE_INPUT_PATH = Path("outputs/active_z2_sigma/bao_scale_free_primitive_inputs.json")
SCALE_FREE_INPUT_PATH = Path("outputs/active_z2_sigma/bao_scale_free_inputs.json")
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_bao_split_primitives_to_scale_free_chi2_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_bao_split_primitives_to_scale_free_chi2_gate.json")


def build_payload(
    background_primitive_path: Path = BACKGROUND_PRIMITIVE_PATH,
    plasma_primitive_path: Path = PLASMA_PRIMITIVE_PATH,
    primitive_input_path: Path = PRIMITIVE_INPUT_PATH,
    scale_free_input_path: Path = SCALE_FREE_INPUT_PATH,
) -> dict:
    assembler = build_primitive_assembler_payload(
        background_primitive_path=background_primitive_path,
        plasma_primitive_path=plasma_primitive_path,
        output_path=primitive_input_path,
    )
    if not assembler["gate_passed"]:
        return {
            "status": "janus-z2-sigma-bao-split-primitives-to-scale-free-chi2-gate",
            "active_core": "Z2_tunnel_Sigma",
            "background_primitive_manifest": str(background_primitive_path),
            "plasma_primitive_manifest": str(plasma_primitive_path),
            "primitive_inputs_assembler_passed": False,
            "primitive_chi2_passed": False,
            "bao_chi2_evaluated": False,
            "chi2_DESI_DR2_BAO": None,
            "uses_compressed_planck_lcdm": False,
            "uses_archived_z4": False,
            "uses_observational_H0_fit": False,
            "gate_passed": False,
            "blocker": assembler["blocker"],
        }

    primitive_chi2 = build_primitive_chi2_payload(
        primitive_input_path=primitive_input_path,
        scale_free_input_path=scale_free_input_path,
    )
    return {
        "status": "janus-z2-sigma-bao-split-primitives-to-scale-free-chi2-gate",
        "active_core": "Z2_tunnel_Sigma",
        "background_primitive_manifest": str(background_primitive_path),
        "plasma_primitive_manifest": str(plasma_primitive_path),
        "primitive_input_manifest": str(primitive_input_path),
        "scale_free_input_manifest": str(scale_free_input_path),
        "primitive_inputs_assembler_passed": True,
        "primitive_chi2_passed": primitive_chi2["gate_passed"],
        "bao_chi2_evaluated": primitive_chi2["bao_chi2_evaluated"],
        "chi2_DESI_DR2_BAO": primitive_chi2.get("chi2_DESI_DR2_BAO"),
        "prediction_vector": primitive_chi2.get("prediction_vector"),
        "residual_vector": primitive_chi2.get("residual_vector"),
        "Gamma_drag_over_H0_Z2Sigma_available": primitive_chi2[
            "Gamma_drag_over_H0_Z2Sigma_available"
        ],
        "uses_compressed_planck_lcdm": False,
        "uses_archived_z4": False,
        "uses_observational_H0_fit": False,
        "gate_passed": primitive_chi2["gate_passed"],
        "blocker": primitive_chi2["blocker"],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma BAO Split Primitives To Scale-Free Chi2 Gate",
        "",
        f"Primitive assembler passed: `{payload['primitive_inputs_assembler_passed']}`",
        f"Primitive chi2 passed: `{payload['primitive_chi2_passed']}`",
        f"BAO chi2 evaluated: `{payload['bao_chi2_evaluated']}`",
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
