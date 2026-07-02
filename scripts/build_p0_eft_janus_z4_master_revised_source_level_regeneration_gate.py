from __future__ import annotations

import json
import sys
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from janus_lab.z4_source_level import hash_payload
from scripts.build_p0_eft_janus_z4_master_highl_acoustic_revision_scan_gate import (
    build_payload as revision_scan_payload,
)
from scripts.build_p0_eft_janus_z4_master_source_level_regeneration_gate import _source_payload


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_master_revised_source_level_regeneration_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_master_revised_source_level_regeneration_gate.json")
MASTER_REVISED_SOURCE_VERSION = "janus-z4-unique-master-source-level-v2-shared-u-silk-guard"


def build_revised_source_payload() -> dict:
    scan = revision_scan_payload()
    best = scan["best_revision"]
    if not best:
        raise RuntimeError("Cannot build revised source without a selected high-l revision")
    source = _source_payload()
    ell = np.asarray(source["projection_grid"], dtype=float)
    raw_u = np.asarray(source["U_Z4"], dtype=float)
    strength = float(best["silk_guard_strength"])
    center = float(best["silk_guard_center_ell"])
    scale = max(float(np.max(np.abs(raw_u))), 1.0e-30)
    guard = 1.0 - strength / (1.0 + np.exp(-(ell - center) / 120.0))
    u_z4 = raw_u * guard / scale
    du = np.gradient(u_z4, ell)
    ddu = np.gradient(du, ell)
    return {
        "version": MASTER_REVISED_SOURCE_VERSION,
        "parent_source_version": source["version"],
        "selected_revision": "shared_U_norm_silk_guard",
        "silk_guard_strength": strength,
        "silk_guard_center_ell": center,
        "projection_grid": ell.tolist(),
        "U_Z4_raw": raw_u.tolist(),
        "U_Z4_silk_guard": guard.tolist(),
        "U_Z4_shared_scale": scale,
        "U_Z4": u_z4.tolist(),
        "S_T_Z4": (u_z4 + 0.18 * du).tolist(),
        "S_E_Z4": (0.72 * u_z4 - 0.22 * du + 0.05 * ddu).tolist(),
        "S_lens_Z4": (0.45 * u_z4 + 0.1 * du).tolist(),
        "Doppler_Z4": du.tolist(),
        "Theta0_Z4": (0.62 * u_z4).tolist(),
        "Pi_Z4": (0.32 * u_z4 - 0.12 * du).tolist(),
        "Slip_Z4": (0.25 * u_z4 + 0.08 * du).tolist(),
        "minus_sector_variables": (u_z4 - 0.3 * du).tolist(),
    }


def build_payload() -> dict:
    scan = revision_scan_payload()
    best = scan["best_revision"]
    source = build_revised_source_payload()
    source_hash = hash_payload(source)
    return {
        "status": "janus-z4-master-revised-source-level-regeneration-gate",
        "revision_scan_passed": scan["revision_found"],
        "selected_revision": source["selected_revision"],
        "selected_revision_parallel_fraction": best["parallel_fraction"],
        "selected_revision_highl_reduction_factor": best["highl_reduction_factor"],
        "source_level_version": MASTER_REVISED_SOURCE_VERSION,
        "master_revised_source_payload_hash": source_hash,
        "U_Z4_revised_from_selected_revision": True,
        "shared_U_Z4_normalization_applied": True,
        "silk_guard_applied_upstream": True,
        "S_T_Z4_regenerated_from_revised_U_Z4": True,
        "S_E_Z4_regenerated_from_revised_U_Z4": True,
        "S_lens_Z4_regenerated_from_revised_U_Z4": True,
        "Doppler_Z4_regenerated_from_revised_U_Z4": True,
        "Theta0_Z4_regenerated_from_revised_U_Z4": True,
        "Pi_Z4_regenerated_from_revised_U_Z4": True,
        "Slip_Z4_regenerated_from_revised_U_Z4": True,
        "minus_sector_variables_regenerated_from_revised_U_Z4": True,
        "all_revised_sources_share_same_U_Z4_hash": True,
        "downstream_patch_allowed": False,
        "independent_downstream_source_allowed": False,
        "lambda_retuning_allowed": False,
        "spectra_generation_allowed": False,
        "observed_Planck_rerun_allowed": False,
        "candidate_promotion_allowed": False,
        "next_required_gate": "P0EFTJanusZ4MasterRevisedCarrierTangentProjectionGate",
        "profiled_planck_candidate": False,
        "full_planck_validation": False,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z4 Master Revised Source-Level Regeneration Gate",
        "",
        f"Revision scan passed: `{payload['revision_scan_passed']}`",
        f"Selected revision: `{payload['selected_revision']}`",
        f"Revision parallel fraction: `{payload['selected_revision_parallel_fraction']}`",
        f"Revision high-l reduction: `{payload['selected_revision_highl_reduction_factor']}`",
        f"Source version: `{payload['source_level_version']}`",
        f"Planck rerun allowed: `{payload['observed_Planck_rerun_allowed']}`",
        f"Next gate: `{payload['next_required_gate']}`",
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
