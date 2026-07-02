from __future__ import annotations

import csv
import json
import sys
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from janus_lab.z4_regenerative_camb_provider import CosmologyPoint, generate_camb_gr_rows, write_spectra
from janus_lab.z4_source_level import hash_payload
from scripts.build_p0_eft_janus_z4_carrier_tangent_projection_gate import _flatten, _rows_to_arrays
from scripts.build_p0_eft_janus_z4_derived_slip_carrier_tangent_projection_gate import CHANNELS, _projection_stats, _tangent_matrix
from scripts.build_p0_eft_janus_z4_master_source_level_regeneration_gate import _source_payload
from scripts.build_p0_eft_janus_z4_two_sector_source_construction_audit_gate import _unit


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_master_diagnostic_spectra_generation_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_master_diagnostic_spectra_generation_gate.json")
SPECTRA_DIR = Path("outputs/reports/z4_master_diagnostic_spectra")


def _interp(values: list[float], ell: np.ndarray) -> np.ndarray:
    x = np.linspace(float(ell[0]), float(ell[-1]), len(values))
    return np.interp(ell, x, np.asarray(values, dtype=float))


def _read_rows(path: Path) -> list[dict[str, float]]:
    with path.open(newline="", encoding="utf-8") as handle:
        return [
            {key: (int(value) if key == "ell" else float(value)) for key, value in row.items()}
            for row in csv.DictReader(handle)
        ]


def build_payload() -> dict:
    source = _source_payload()
    reference = generate_camb_gr_rows(CosmologyPoint())
    arrays = _rows_to_arrays(reference)
    ell = arrays["ell"]
    s_t = _unit(_interp(source["S_T_Z4"], ell))
    s_e = _unit(_interp(source["S_E_Z4"], ell))
    doppler = _unit(_interp(source["Doppler_Z4"], ell))
    pi = _unit(_interp(source["Pi_Z4"], ell))
    delta = {
        "cl_tt": arrays["cl_tt"] * (s_t + 0.15 * doppler),
        "cl_te": arrays["cl_te"] * (0.5 * s_t + 0.5 * s_e),
        "cl_ee": arrays["cl_ee"] * (s_e + 0.2 * pi),
    }
    candidate = []
    for i, row in enumerate(reference):
        candidate.append(
            {
                "ell": int(row["ell"]),
                "cl_tt": float(row["cl_tt"] + delta["cl_tt"][i]),
                "cl_te": float(row["cl_te"] + delta["cl_te"][i]),
                "cl_ee": float(row["cl_ee"] + delta["cl_ee"][i]),
                "cl_pp": float(row["cl_pp"]),
            }
        )

    SPECTRA_DIR.mkdir(parents=True, exist_ok=True)
    baseline_path = SPECTRA_DIR / "reference_gr.csv"
    candidate_path = SPECTRA_DIR / "reference_gr_plus_master_z4.csv"
    write_spectra(baseline_path, reference)
    write_spectra(candidate_path, candidate)

    replay_rows = _read_rows(candidate_path)
    replay_arrays = _rows_to_arrays(replay_rows)
    scales = {channel: float(np.sqrt(np.mean(np.square(arrays[channel]))) or 1.0) for channel in CHANNELS}
    matrix, tangent_norms = _tangent_matrix(reference, scales)
    replay_delta = {channel: replay_arrays[channel] - arrays[channel] for channel in CHANNELS}
    stats = _projection_stats(_flatten(replay_delta, scales), matrix, tangent_norms)
    parallel = stats["parallel_fraction"]
    return {
        "status": "janus-z4-master-diagnostic-spectra-generation-gate",
        "diagnostic_spectra_readiness_gate_passed": True,
        "source_payload_hash": hash_payload(source),
        "baseline_spectra_path": str(baseline_path),
        "candidate_spectra_path": str(candidate_path),
        "diagnostic_spectra_generated": True,
        "source_level_payload_replayed_after_serialization": True,
        "parallel_fraction_after_serialization": parallel,
        "perpendicular_fraction_after_serialization": stats["perpendicular_fraction"],
        "dominant_tangent_direction_after_serialization": stats["dominant_tangent_direction"],
        "passes_success_threshold_lt_0p7": parallel < 0.7,
        "passes_strong_threshold_lt_0p5": parallel < 0.5,
        "official_planck_trial_allowed": False,
        "likelihood_evaluation_allowed": False,
        "candidate_promotion_allowed": False,
        "lambda_retuning_allowed": False,
        "next_required_gate": "P0EFTJanusZ4MasterDiagnosticShapeReportGate",
        "profiled_planck_candidate": False,
        "full_planck_validation": False,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z4 Master Diagnostic Spectra Generation Gate",
        "",
        f"Diagnostic spectra generated: `{payload['diagnostic_spectra_generated']}`",
        f"Parallel after serialization: `{payload['parallel_fraction_after_serialization']}`",
        f"Official Planck allowed: `{payload['official_planck_trial_allowed']}`",
        f"Next gate: `{payload['next_required_gate']}`",
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
