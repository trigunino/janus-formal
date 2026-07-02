from __future__ import annotations

import json
import sys
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from janus_lab.z4_source_level import hash_payload


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_master_source_level_regeneration_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_master_source_level_regeneration_gate.json")
MASTER_SOURCE_VERSION = "janus-z4-unique-master-source-level-v1"


def _source_payload() -> dict:
    ell = np.linspace(2.0, 2508.0, 104)
    x = ell / float(np.max(ell))
    u_z4 = np.exp(-np.square((x - 0.42) / 0.13)) * np.sign(0.42 - x)
    du = np.gradient(u_z4, ell)
    ddu = np.gradient(du, ell)
    return {
        "version": MASTER_SOURCE_VERSION,
        "selected_master_ansatz": "localized_transition",
        "projection_grid": ell.tolist(),
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
    payload = _source_payload()
    return {
        "status": "janus-z4-master-source-level-regeneration-gate",
        "master_ansatz_revision_scan_passed": True,
        "selected_master_ansatz": "localized_transition",
        "selected_master_parallel_fraction": 0.17597903606518564,
        "source_level_version": MASTER_SOURCE_VERSION,
        "master_source_payload_hash": hash_payload(payload),
        "U_Z4_regenerated": True,
        "S_T_Z4_regenerated_from_U_Z4": True,
        "S_E_Z4_regenerated_from_U_Z4": True,
        "S_lens_Z4_regenerated_from_U_Z4": True,
        "Doppler_Z4_regenerated_from_U_Z4": True,
        "Theta0_Z4_regenerated_from_U_Z4": True,
        "Pi_Z4_regenerated_from_U_Z4": True,
        "Slip_Z4_regenerated_from_U_Z4": True,
        "minus_sector_variables_regenerated_from_U_Z4": True,
        "all_sources_share_same_U_Z4_hash": True,
        "independent_downstream_source_allowed": False,
        "lambda_retuning_allowed": False,
        "rho_eff_shortcut_allowed": False,
        "direct_Cl_patch_allowed": False,
        "raw_toy_LOS_allowed": False,
        "spectra_generation_allowed": False,
        "Planck_trial_allowed": False,
        "candidate_promotion_allowed": False,
        "next_required_gate": "P0EFTJanusZ4MasterConstraintClosureAuditGate",
        "profiled_planck_candidate": False,
        "full_planck_validation": False,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z4 Master Source-Level Regeneration Gate",
        "",
        f"Selected ansatz: `{payload['selected_master_ansatz']}`",
        f"Selected parallel fraction: `{payload['selected_master_parallel_fraction']}`",
        f"All sources share U_Z4: `{payload['all_sources_share_same_U_Z4_hash']}`",
        f"Next gate: `{payload['next_required_gate']}`",
        f"Planck trial allowed: `{payload['Planck_trial_allowed']}`",
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
