from __future__ import annotations

import csv
import json
import sys
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from janus_lab.z4_regenerative_camb_provider import write_spectra
from scripts.build_p0_eft_janus_z4_master_acoustic_calculator_component_spectra_gate import (
    build_payload as component_payload,
)

REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_master_unlensed_lensed_split_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_master_unlensed_lensed_split_gate.json")
SPLIT_DIR = Path("outputs/reports/z4_master_unlensed_lensed_split")


def _read(path: str) -> list[dict[str, float]]:
    with Path(path).open(newline="", encoding="utf-8") as handle:
        return [
            {key: (int(value) if key == "ell" else float(value)) for key, value in row.items()}
            for row in csv.DictReader(handle)
        ]


def _arrays(rows: list[dict[str, float]]) -> dict[str, np.ndarray]:
    return {key: np.asarray([row[key] for row in rows], dtype=float) for key in ("ell", "cl_tt", "cl_te", "cl_ee", "cl_pp")}


def _rows_from_arrays(arrays: dict[str, np.ndarray]) -> list[dict[str, float]]:
    return [
        {
            "ell": int(arrays["ell"][i]),
            "cl_tt": float(arrays["cl_tt"][i]),
            "cl_te": float(arrays["cl_te"][i]),
            "cl_ee": float(arrays["cl_ee"][i]),
            "cl_pp": float(arrays["cl_pp"][i]),
        }
        for i in range(len(arrays["ell"]))
    ]


def _smooth(values: np.ndarray, width: int = 2) -> np.ndarray:
    if len(values) < 2 * width + 1:
        return values.copy()
    out = values.copy()
    for i in range(width, len(values) - width):
        out[i] = np.mean(values[i - width : i + width + 1])
    return out


def build_payload() -> dict:
    component = component_payload()
    baseline = _arrays(_read(component["baseline_spectra_path"]))
    total = _arrays(_read(component["total_spectra_path"]))
    ell = baseline["ell"]
    remap_strength = np.clip((ell / 2500.0) ** 2, 0.0, 1.0) * 0.035
    lensed = {"ell": ell, "cl_pp": baseline["cl_pp"]}
    for channel in ("cl_tt", "cl_te", "cl_ee"):
        smooth = _smooth(total[channel])
        lensed[channel] = (1.0 - remap_strength) * total[channel] + remap_strength * smooth

    SPLIT_DIR.mkdir(parents=True, exist_ok=True)
    unlensed_path = SPLIT_DIR / "unlensed_total.csv"
    lensed_path = SPLIT_DIR / "lensed_total.csv"
    lensing_kernel_path = SPLIT_DIR / "lensing_kernel.json"
    write_spectra(unlensed_path, _rows_from_arrays(total))
    write_spectra(lensed_path, _rows_from_arrays(lensed))
    lensing_kernel_path.write_text(
        json.dumps(
            {
                "kind": "deterministic_internal_smoothing_remap",
                "input_cl_pp": component["baseline_spectra_path"],
                "remap_strength_max": float(np.max(remap_strength)),
                "physical_lensing_solver": False,
            },
            indent=2,
        ),
        encoding="utf-8",
    )
    return {
        "status": "janus-z4-master-unlensed-lensed-split-gate",
        "component_spectra_gate_passed": component["internal_diagnostic_spectra_generated"],
        "unlensed_spectra_path": str(unlensed_path),
        "lensed_spectra_path": str(lensed_path),
        "lensing_kernel_path": str(lensing_kernel_path),
        "unlensed_source_spectra_generated": True,
        "lensed_remap_generated": True,
        "unlensed_lensed_split_available": True,
        "lensed_remap_policy": "deterministic_internal_smoothing_remap",
        "physical_lensing_solver": False,
        "observed_likelihood_allowed": False,
        "planck_retry_allowed": False,
        "candidate_promotion_allowed": False,
        "retuning_allowed": False,
        "full_planck_validation": False,
        "next_required_gate": "P0EFTJanusZ4MasterLensingRemapPolicyGate",
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z4 Master Unlensed/Lensed Split Gate",
        "",
        f"Split available: `{payload['unlensed_lensed_split_available']}`",
        f"Unlensed spectra: `{payload['unlensed_spectra_path']}`",
        f"Lensed spectra: `{payload['lensed_spectra_path']}`",
        f"Physical lensing solver: `{payload['physical_lensing_solver']}`",
        f"Planck retry allowed: `{payload['planck_retry_allowed']}`",
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
