from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from janus_lab.z2_sigma_active_inputs import load_active_z2sigma_bao_inputs
from scripts.build_p0_eft_janus_z2_sigma_background_scalar_manifest_writer_from_inputs_gate import (
    build_payload as build_background_writer_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_bao_active_manifest_pipeline_gate import (
    build_payload as build_active_pipeline_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_bao_component_manifest_writer_gate import (
    build_payload as build_component_writer_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_bao_official_chi2_gate import (
    build_payload as build_official_chi2_payload,
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
BAO_INPUT_PATH = Path("outputs/active_z2_sigma/bao_inputs.json")
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_active_inputs_to_official_bao_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_active_inputs_to_official_bao_gate.json")


def build_payload(
    *,
    background_input_path: Path = BACKGROUND_INPUT_PATH,
    flrw_input_path: Path = FLRW_INPUT_PATH,
    early_input_path: Path = EARLY_INPUT_PATH,
    background_manifest_path: Path = BACKGROUND_MANIFEST_PATH,
    flrw_manifest_path: Path = FLRW_MANIFEST_PATH,
    early_manifest_path: Path = EARLY_MANIFEST_PATH,
    component_manifest_path: Path = COMPONENT_MANIFEST_PATH,
    bao_input_path: Path = BAO_INPUT_PATH,
) -> dict:
    required_inputs = {
        "background_scalar_inputs": {
            "path": str(background_input_path),
            "exists": background_input_path.exists(),
        },
        "flrw_component_inputs": {
            "path": str(flrw_input_path),
            "exists": flrw_input_path.exists(),
        },
        "early_plasma_inputs": {
            "path": str(early_input_path),
            "exists": early_input_path.exists(),
        },
    }
    required_inputs_available = all(item["exists"] for item in required_inputs.values())
    if not required_inputs_available:
        return {
            "status": "janus-z2-sigma-active-inputs-to-official-bao-gate",
            "active_core": "Z2_tunnel_Sigma",
            "required_input_manifests": required_inputs,
            "required_input_manifests_available": False,
            "atomic_preflight_passed": False,
            "background_scalar_manifest_written": False,
            "flrw_component_manifest_written": False,
            "early_plasma_manifest_written": False,
            "bao_component_manifest_written": False,
            "bao_input_manifest_written": False,
            "active_bao_input_valid": False,
            "official_bao_evaluation": False,
            "bao_chi2_evaluated": False,
            "chi2_DESI_DR2_BAO": None,
            "uses_compressed_planck_lcdm": False,
            "uses_archived_z4": False,
            "uses_phenomenological_holst_bao_scan": False,
            "gate_passed": False,
            "blocker": "missing active-derived input manifests",
        }

    counterterm = build_counterterm_frontier_payload()
    if not counterterm["counterterm_radial_reduction_ready"]:
        return {
            "status": "janus-z2-sigma-active-inputs-to-official-bao-gate",
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
            "bao_input_manifest_written": False,
            "active_bao_input_valid": False,
            "official_bao_evaluation": False,
            "bao_chi2_evaluated": False,
            "chi2_DESI_DR2_BAO": None,
            "uses_compressed_planck_lcdm": False,
            "uses_archived_z4": False,
            "uses_phenomenological_holst_bao_scan": False,
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
    active_pipeline = build_active_pipeline_payload(
        component_input_path=component_manifest_path,
        output_manifest_path=bao_input_path,
    )
    official = build_official_chi2_payload(bao_input_path)
    try:
        load_active_z2sigma_bao_inputs(bao_input_path)
        active_bao_input_valid = True
    except Exception:
        active_bao_input_valid = False

    return {
        "status": "janus-z2-sigma-active-inputs-to-official-bao-gate",
        "active_core": "Z2_tunnel_Sigma",
        "required_input_manifests": required_inputs,
        "required_input_manifests_available": True,
        "atomic_preflight_passed": True,
        "background_scalar_manifest_written": background["manifest_written"],
        "flrw_component_manifest_written": flrw["manifest_written"],
        "early_plasma_manifest_written": early["manifest_written"],
        "bao_component_manifest_written": component["official_component_manifest_written"],
        "bao_input_manifest_written": active_pipeline["bao_input_manifest_written"],
        "active_bao_input_valid": active_bao_input_valid,
        "official_bao_evaluation": official["official_bao_evaluation"],
        "bao_chi2_evaluated": official["bao_chi2_evaluated"],
        "chi2_DESI_DR2_BAO": official.get("chi2_DESI_DR2_BAO"),
        "uses_compressed_planck_lcdm": False,
        "uses_archived_z4": False,
        "uses_phenomenological_holst_bao_scan": False,
        "gate_passed": bool(official["bao_official_chi2_gate_passed"]),
        "blocker": None if official["bao_official_chi2_gate_passed"] else official.get("blocker", "upstream active inputs incomplete"),
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Active Inputs To Official BAO Gate",
        "",
        f"BAO component manifest written: `{payload['bao_component_manifest_written']}`",
        f"BAO input manifest written: `{payload['bao_input_manifest_written']}`",
        f"Official BAO evaluation: `{payload['official_bao_evaluation']}`",
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
