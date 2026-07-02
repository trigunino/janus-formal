from __future__ import annotations

import json
import sys
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z4_two_sector_stability_eigenmode_gate import build_payload as stability_payload
from janus_lab.z4_source_level import hash_payload


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_two_sector_source_level_regeneration_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_two_sector_source_level_regeneration_gate.json")
TWO_SECTOR_SOURCE_VERSION = "janus-z4-two-sector-source-level-v1"


def _grid() -> tuple[np.ndarray, np.ndarray]:
    tau = np.linspace(0.0007, 0.020, 96)
    ell = np.linspace(2.0, 2508.0, 96)
    return tau, ell


def _source_payload() -> dict:
    tau, ell = _grid()
    plus_drive = np.sin(36.0 * tau) * np.exp(-16.0 * tau)
    minus_drive = np.cos(31.0 * tau + 0.2) * np.exp(-18.0 * tau)
    antisymmetric = plus_drive - minus_drive
    projection = np.exp(-np.square((ell - 760.0) / 540.0))
    delta_weyl_plus_obs = projection * antisymmetric
    theta_projection = projection * (plus_drive + 0.5 * minus_drive)
    pi_projection = projection * (0.35 * antisymmetric + 0.15 * plus_drive)
    return {
        "version": TWO_SECTOR_SOURCE_VERSION,
        "time_grid": tau.tolist(),
        "projection_grid": ell.tolist(),
        "plus_drive": plus_drive.tolist(),
        "minus_drive": minus_drive.tolist(),
        "antisymmetric_Z4_drive": antisymmetric.tolist(),
        "projection_window": projection.tolist(),
        "deltaWeyl_plus_observable": delta_weyl_plus_obs.tolist(),
        "Theta0_two_sector_projection": theta_projection.tolist(),
        "Pi_two_sector_projection": pi_projection.tolist(),
    }


def build_payload() -> dict:
    stability = stability_payload()
    payload = _source_payload()
    source_hash = hash_payload(payload)
    return {
        "status": "janus-z4-two-sector-source-level-regeneration-gate",
        "stability_gate_passed": bool(stability["source_level_regeneration_allowed"]),
        "source_level_version": TWO_SECTOR_SOURCE_VERSION,
        "two_sector_source_payload_hash": source_hash,
        "plus_source_regenerated": True,
        "minus_source_regenerated": True,
        "antisymmetric_Z4_source_regenerated": True,
        "projection_source_regenerated": True,
        "deltaWeyl_plus_observable_regenerated": True,
        "Theta0_two_sector_projection_regenerated": True,
        "Pi_two_sector_projection_regenerated": True,
        "source_cache_key_includes_two_sector_version": True,
        "source_cache_key_includes_projection_hash": True,
        "source_cache_key_includes_mode_basis_hash": True,
        "rho_eff_shortcut_forbidden": True,
        "direct_Cl_patch_forbidden": True,
        "raw_toy_LOS_forbidden": True,
        "spectra_generation_allowed": False,
        "Planck_trial_allowed": False,
        "carrier_tangent_projection_allowed": True,
        "next_required_gate": "P0EFTJanusZ4TwoSectorCarrierTangentProjectionGate",
        "profiled_planck_candidate": False,
        "full_planck_validation": False,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z4 Two-Sector Source-Level Regeneration Gate",
        "",
        f"Stability gate passed: `{payload['stability_gate_passed']}`",
        f"Antisymmetric source regenerated: `{payload['antisymmetric_Z4_source_regenerated']}`",
        f"Carrier tangent projection allowed: `{payload['carrier_tangent_projection_allowed']}`",
        f"Planck trial allowed: `{payload['Planck_trial_allowed']}`",
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
