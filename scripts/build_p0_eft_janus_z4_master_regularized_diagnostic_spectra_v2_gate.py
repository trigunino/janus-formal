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
from scripts.build_p0_eft_janus_z4_master_diagnostic_spectra_generation_gate import _interp
from scripts.build_p0_eft_janus_z4_master_revised_carrier_tangent_projection_gate import (
    _revised_source_shapes,
    build_payload as tangent_payload,
)
from scripts.build_p0_eft_janus_z4_master_revised_source_level_regeneration_gate import (
    build_revised_source_payload,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_master_regularized_diagnostic_spectra_v2_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_master_regularized_diagnostic_spectra_v2_gate.json")
SPECTRA_DIR = Path("outputs/reports/z4_master_regularized_diagnostic_spectra_v2")


def _read_rows(path: Path) -> list[dict[str, float]]:
    with path.open(newline="", encoding="utf-8") as handle:
        return [
            {key: (int(value) if key == "ell" else float(value)) for key, value in row.items()}
            for row in csv.DictReader(handle)
        ]


def build_payload() -> dict:
    tangent = tangent_payload()
    source = build_revised_source_payload()
    reference = generate_camb_gr_rows(CosmologyPoint())
    arrays = _rows_to_arrays(reference)
    ell = arrays["ell"]
    shapes = _revised_source_shapes(source, ell)
    delta = {channel: arrays[channel] * shapes[channel] for channel in CHANNELS}
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
    candidate_path = SPECTRA_DIR / "reference_gr_plus_master_z4_v2.csv"
    write_spectra(baseline_path, reference)
    write_spectra(candidate_path, candidate)

    replay_arrays = _rows_to_arrays(_read_rows(candidate_path))
    replay_delta = {channel: replay_arrays[channel] - arrays[channel] for channel in CHANNELS}
    scales = {channel: float(np.sqrt(np.mean(np.square(arrays[channel]))) or 1.0) for channel in CHANNELS}
    matrix, tangent_norms = _tangent_matrix(reference, scales)
    stats = _projection_stats(_flatten(replay_delta, scales), matrix, tangent_norms)
    source_shape_norms = {
        channel: float(np.sqrt(np.mean(np.square(_interp(source[key], ell)))))
        for channel, key in {
            "cl_tt": "S_T_Z4",
            "cl_te": "S_E_Z4",
            "cl_ee": "Pi_Z4",
        }.items()
    }
    return {
        "status": "janus-z4-master-regularized-diagnostic-spectra-v2-gate",
        "revised_carrier_tangent_projection_passed": tangent["carrier_threshold_passed"],
        "source_level_version": source["version"],
        "source_payload_hash": hash_payload(source),
        "baseline_spectra_path": str(baseline_path),
        "candidate_spectra_path": str(candidate_path),
        "diagnostic_spectra_v2_generated": True,
        "source_level_payload_replayed_after_serialization": True,
        "parallel_fraction_after_serialization": stats["parallel_fraction"],
        "perpendicular_fraction_after_serialization": stats["perpendicular_fraction"],
        "dominant_tangent_direction_after_serialization": stats["dominant_tangent_direction"],
        "source_shape_norms": source_shape_norms,
        "passes_carrier_threshold_lt_0p7": stats["parallel_fraction"] < 0.7,
        "passes_strong_threshold_lt_0p5": stats["parallel_fraction"] < 0.5,
        "official_planck_trial_allowed": False,
        "likelihood_evaluation_allowed": False,
        "candidate_promotion_allowed": False,
        "next_required_gate": "P0EFTJanusZ4MasterDiagnosticShapeReportV2Gate",
        "profiled_planck_candidate": False,
        "full_planck_validation": False,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z4 Master Regularized Diagnostic Spectra V2 Gate",
        "",
        f"Generated: `{payload['diagnostic_spectra_v2_generated']}`",
        f"Parallel fraction: `{payload['parallel_fraction_after_serialization']}`",
        f"Official Planck allowed: `{payload['official_planck_trial_allowed']}`",
        f"Next gate: `{payload['next_required_gate']}`",
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
