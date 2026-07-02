from __future__ import annotations

import json
import sys
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from janus_lab.z4_regenerative_camb_provider import CosmologyPoint, generate_camb_gr_rows
from scripts.build_p0_eft_janus_z4_carrier_tangent_projection_gate import _flatten, _rows_to_arrays
from scripts.build_p0_eft_janus_z4_derived_slip_carrier_tangent_projection_gate import CHANNELS, _projection_stats, _tangent_matrix
from scripts.build_p0_eft_janus_z4_two_sector_source_construction_audit_gate import _delta, _unit


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_master_carrier_tangent_projection_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_master_carrier_tangent_projection_gate.json")
SUCCESS_THRESHOLD = 0.70
STRONG_THRESHOLD = 0.50
ARCHIVE_THRESHOLD = 0.80


def _master_u(ell: np.ndarray) -> np.ndarray:
    x = ell / float(np.max(ell))
    return np.sin(14.0 * x + 0.3) * np.exp(-1.15 * x) * (1.0 - 0.55 * x)


def build_payload() -> dict:
    reference = generate_camb_gr_rows(CosmologyPoint())
    arrays = _rows_to_arrays(reference)
    ell = arrays["ell"]
    scales = {channel: float(np.sqrt(np.mean(np.square(arrays[channel]))) or 1.0) for channel in CHANNELS}
    matrix, tangent_norms = _tangent_matrix(reference, scales)

    u_z4 = _unit(_master_u(ell))
    master_delta = {
        "cl_tt": arrays["cl_tt"] * u_z4,
        "cl_te": arrays["cl_te"] * (0.72 * u_z4 + 0.18 * np.gradient(u_z4, ell)),
        "cl_ee": arrays["cl_ee"] * (0.48 * u_z4 - 0.22 * np.gradient(u_z4, ell)),
    }
    stats = _projection_stats(_flatten(master_delta, scales), matrix, tangent_norms)
    parallel = stats["parallel_fraction"]
    return {
        "status": "janus-z4-master-carrier-tangent-projection-gate",
        "master_to_observable_map_gate_passed": True,
        "master_signal_source": "single_U_Z4_diagnostic",
        "all_channels_derived_from_same_U_Z4": True,
        "channels_projected": list(CHANNELS),
        "parallel_fraction": parallel,
        "perpendicular_fraction": stats["perpendicular_fraction"],
        "dominant_tangent_direction": stats["dominant_tangent_direction"],
        "tangent_contribution_scores": stats["tangent_contribution_scores"],
        "passes_success_threshold_lt_0p7": parallel < SUCCESS_THRESHOLD,
        "passes_strong_threshold_lt_0p5": parallel < STRONG_THRESHOLD,
        "archive_current_master_ansatz": parallel > ARCHIVE_THRESHOLD,
        "beats_archived_patchwork_branches": parallel < 0.904,
        "spectra_generation_allowed": False,
        "Planck_trial_allowed": False,
        "candidate_promotion_allowed": False,
        "next_required_gate": "P0EFTJanusZ4MasterSourceLevelRegenerationGate" if parallel < SUCCESS_THRESHOLD else "revise_unique_Z4_master_ansatz",
        "profiled_planck_candidate": False,
        "full_planck_validation": False,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z4 Master Carrier Tangent Projection Gate",
        "",
        f"Parallel fraction: `{payload['parallel_fraction']}`",
        f"Dominant tangent: `{payload['dominant_tangent_direction']}`",
        f"Passes <0.7: `{payload['passes_success_threshold_lt_0p7']}`",
        f"Archive current ansatz: `{payload['archive_current_master_ansatz']}`",
        f"Next gate: `{payload['next_required_gate']}`",
        f"Planck trial allowed: `{payload['Planck_trial_allowed']}`",
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
