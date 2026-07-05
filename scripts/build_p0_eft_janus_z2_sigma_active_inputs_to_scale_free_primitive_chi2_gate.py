from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z2_sigma_background_scalar_manifest_writer_from_inputs_gate import (
    build_payload as build_background_writer_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_bao_component_manifest_writer_gate import (
    build_payload as build_component_writer_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_bao_component_to_scale_free_primitive_chi2_gate import (
    build_payload as build_component_to_primitive_chi2_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_early_plasma_manifest_writer_from_inputs_gate import (
    build_payload as build_early_writer_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_flrw_component_manifest_writer_from_inputs_gate import (
    build_payload as build_flrw_writer_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_counterterm_radial_reduction_frontier_gate import (
    build_payload as build_counterterm_frontier_payload,
)


BACKGROUND_INPUT_PATH = Path("outputs/active_z2_sigma/background_scalar_inputs.json")
FLRW_INPUT_PATH = Path("outputs/active_z2_sigma/flrw_component_inputs.json")
EARLY_INPUT_PATH = Path("outputs/active_z2_sigma/early_plasma_inputs.json")
BACKGROUND_MANIFEST_PATH = Path("outputs/active_z2_sigma/background_scalars.json")
FLRW_MANIFEST_PATH = Path("outputs/active_z2_sigma/flrw_components.json")
EARLY_MANIFEST_PATH = Path("outputs/active_z2_sigma/early_plasma.json")
COMPONENT_MANIFEST_PATH = Path("outputs/active_z2_sigma/bao_component_inputs.json")
BACKGROUND_PRIMITIVE_PATH = Path("outputs/active_z2_sigma/bao_scale_free_background_primitive_inputs.json")
PLASMA_PRIMITIVE_PATH = Path("outputs/active_z2_sigma/bao_scale_free_plasma_primitive_inputs.json")
PRIMITIVE_INPUT_PATH = Path("outputs/active_z2_sigma/bao_scale_free_primitive_inputs.json")
SCALE_FREE_INPUT_PATH = Path("outputs/active_z2_sigma/bao_scale_free_inputs.json")
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_active_inputs_to_scale_free_primitive_chi2_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_active_inputs_to_scale_free_primitive_chi2_gate.json")


def build_payload(
    *,
    background_input_path: Path = BACKGROUND_INPUT_PATH,
    flrw_input_path: Path = FLRW_INPUT_PATH,
    early_input_path: Path = EARLY_INPUT_PATH,
    background_manifest_path: Path = BACKGROUND_MANIFEST_PATH,
    flrw_manifest_path: Path = FLRW_MANIFEST_PATH,
    early_manifest_path: Path = EARLY_MANIFEST_PATH,
    component_manifest_path: Path = COMPONENT_MANIFEST_PATH,
    background_primitive_path: Path = BACKGROUND_PRIMITIVE_PATH,
    plasma_primitive_path: Path = PLASMA_PRIMITIVE_PATH,
    primitive_input_path: Path = PRIMITIVE_INPUT_PATH,
    scale_free_input_path: Path = SCALE_FREE_INPUT_PATH,
) -> dict:
    required_inputs = {
        "background_scalar_inputs": {"path": str(background_input_path), "exists": background_input_path.exists()},
        "flrw_component_inputs": {"path": str(flrw_input_path), "exists": flrw_input_path.exists()},
        "early_plasma_inputs": {"path": str(early_input_path), "exists": early_input_path.exists()},
    }
    if not all(item["exists"] for item in required_inputs.values()):
        return {
            "status": "janus-z2-sigma-active-inputs-to-scale-free-primitive-chi2-gate",
            "active_core": "Z2_tunnel_Sigma",
            "required_input_manifests": required_inputs,
            "required_input_manifests_available": False,
            "atomic_preflight_passed": False,
            "background_scalar_manifest_written": False,
            "flrw_component_manifest_written": False,
            "early_plasma_manifest_written": False,
            "bao_component_manifest_written": False,
            "primitive_chain_executed": False,
            "bao_chi2_evaluated": False,
            "chi2_DESI_DR2_BAO": None,
            "uses_compressed_planck_lcdm": False,
            "uses_archived_z4": False,
            "uses_observational_H0_fit": False,
            "gate_passed": False,
            "blocker": "missing active-derived input manifests",
        }

    counterterm = build_counterterm_frontier_payload()
    if not counterterm["counterterm_radial_reduction_ready"]:
        return {
            "status": "janus-z2-sigma-active-inputs-to-scale-free-primitive-chi2-gate",
            "active_core": "Z2_tunnel_Sigma",
            "required_input_manifests": required_inputs,
            "required_input_manifests_available": True,
            "counterterm_radial_reduction_ready": False,
            "counterterm_current_frontier": counterterm["current_frontier"],
            "atomic_preflight_passed": False,
            "background_scalar_manifest_written": False,
            "flrw_component_manifest_written": False,
            "early_plasma_manifest_written": False,
            "bao_component_manifest_written": False,
            "primitive_chain_executed": False,
            "primitive_inputs_assembler_passed": False,
            "primitive_chi2_passed": False,
            "bao_chi2_evaluated": False,
            "chi2_DESI_DR2_BAO": None,
            "Gamma_drag_over_H0_Z2Sigma_available": False,
            "uses_compressed_planck_lcdm": False,
            "uses_archived_z4": False,
            "uses_observational_H0_fit": False,
            "gate_passed": False,
            "blocker": "counterterm density/rho_p not derived from active Sigma radial reduction",
        }

    background = build_background_writer_payload(
        input_path=background_input_path,
        manifest_path=background_manifest_path,
    )
    flrw = build_flrw_writer_payload(
        input_path=flrw_input_path,
        manifest_path=flrw_manifest_path,
    )
    early = build_early_writer_payload(
        input_path=early_input_path,
        manifest_path=early_manifest_path,
    )
    component = build_component_writer_payload(
        background_scalar_path=background_manifest_path,
        flrw_component_path=flrw_manifest_path,
        early_plasma_path=early_manifest_path,
        component_manifest_path=component_manifest_path,
    )
    primitive_chain = build_component_to_primitive_chi2_payload(
        component_manifest_path=component_manifest_path,
        background_primitive_path=background_primitive_path,
        plasma_primitive_path=plasma_primitive_path,
        primitive_input_path=primitive_input_path,
        scale_free_input_path=scale_free_input_path,
    )
    return {
        "status": "janus-z2-sigma-active-inputs-to-scale-free-primitive-chi2-gate",
        "active_core": "Z2_tunnel_Sigma",
        "required_input_manifests": required_inputs,
        "required_input_manifests_available": True,
        "atomic_preflight_passed": True,
        "background_scalar_manifest_written": background["manifest_written"],
        "flrw_component_manifest_written": flrw["manifest_written"],
        "early_plasma_manifest_written": early["manifest_written"],
        "bao_component_manifest_written": component["official_component_manifest_written"],
        "primitive_chain_executed": primitive_chain["component_to_split_primitives_passed"],
        "primitive_inputs_assembler_passed": primitive_chain["primitive_inputs_assembler_passed"],
        "primitive_chi2_passed": primitive_chain["primitive_chi2_passed"],
        "bao_chi2_evaluated": primitive_chain["bao_chi2_evaluated"],
        "chi2_DESI_DR2_BAO": primitive_chain.get("chi2_DESI_DR2_BAO"),
        "prediction_vector": primitive_chain.get("prediction_vector"),
        "residual_vector": primitive_chain.get("residual_vector"),
        "Gamma_drag_over_H0_Z2Sigma_available": primitive_chain.get(
            "Gamma_drag_over_H0_Z2Sigma_available",
            False,
        ),
        "uses_compressed_planck_lcdm": False,
        "uses_archived_z4": False,
        "uses_observational_H0_fit": False,
        "gate_passed": bool(primitive_chain["gate_passed"]),
        "blocker": primitive_chain["blocker"],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Active Inputs To Scale-Free Primitive Chi2 Gate",
        "",
        f"Atomic preflight passed: `{payload['atomic_preflight_passed']}`",
        f"BAO component manifest written: `{payload['bao_component_manifest_written']}`",
        f"Primitive chain executed: `{payload['primitive_chain_executed']}`",
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
