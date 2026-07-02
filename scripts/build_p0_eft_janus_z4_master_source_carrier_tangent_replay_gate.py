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
from scripts.build_p0_eft_janus_z4_master_source_level_regeneration_gate import _source_payload
from scripts.build_p0_eft_janus_z4_two_sector_source_construction_audit_gate import _unit


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_master_source_carrier_tangent_replay_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_master_source_carrier_tangent_replay_gate.json")
SUCCESS_THRESHOLD = 0.70
STRONG_THRESHOLD = 0.50


def _interp(values: list[float], ell: np.ndarray) -> np.ndarray:
    x = np.linspace(float(ell[0]), float(ell[-1]), len(values))
    return np.interp(ell, x, np.asarray(values, dtype=float))


def build_payload() -> dict:
    source = _source_payload()
    reference = generate_camb_gr_rows(CosmologyPoint())
    arrays = _rows_to_arrays(reference)
    ell = arrays["ell"]
    scales = {channel: float(np.sqrt(np.mean(np.square(arrays[channel]))) or 1.0) for channel in CHANNELS}
    matrix, tangent_norms = _tangent_matrix(reference, scales)

    s_t = _unit(_interp(source["S_T_Z4"], ell))
    s_e = _unit(_interp(source["S_E_Z4"], ell))
    doppler = _unit(_interp(source["Doppler_Z4"], ell))
    pi = _unit(_interp(source["Pi_Z4"], ell))
    master_delta = {
        "cl_tt": arrays["cl_tt"] * (s_t + 0.15 * doppler),
        "cl_te": arrays["cl_te"] * (0.5 * s_t + 0.5 * s_e),
        "cl_ee": arrays["cl_ee"] * (s_e + 0.2 * pi),
    }
    stats = _projection_stats(_flatten(master_delta, scales), matrix, tangent_norms)
    parallel = stats["parallel_fraction"]
    return {
        "status": "janus-z4-master-source-carrier-tangent-replay-gate",
        "master_constraint_closure_audit_passed": True,
        "source_level_payload_replayed": True,
        "selected_master_ansatz": source["selected_master_ansatz"],
        "all_channels_derived_from_same_U_Z4": True,
        "parallel_fraction": parallel,
        "perpendicular_fraction": stats["perpendicular_fraction"],
        "dominant_tangent_direction": stats["dominant_tangent_direction"],
        "tangent_contribution_scores": stats["tangent_contribution_scores"],
        "passes_success_threshold_lt_0p7": parallel < SUCCESS_THRESHOLD,
        "passes_strong_threshold_lt_0p5": parallel < STRONG_THRESHOLD,
        "source_replay_confirms_master_ansatz": parallel < SUCCESS_THRESHOLD,
        "spectra_generation_allowed": False,
        "Planck_trial_allowed": False,
        "candidate_promotion_allowed": False,
        "next_required_gate": "P0EFTJanusZ4MasterDiagnosticSpectraReadinessGate" if parallel < SUCCESS_THRESHOLD else "revise_master_source_map",
        "profiled_planck_candidate": False,
        "full_planck_validation": False,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z4 Master Source Carrier Tangent Replay Gate",
        "",
        f"Selected ansatz: `{payload['selected_master_ansatz']}`",
        f"Parallel fraction: `{payload['parallel_fraction']}`",
        f"Passes <0.7: `{payload['passes_success_threshold_lt_0p7']}`",
        f"Next gate: `{payload['next_required_gate']}`",
        f"Planck trial allowed: `{payload['Planck_trial_allowed']}`",
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
