from __future__ import annotations

from pathlib import Path
import json

import numpy as np

try:
    from scripts.build_kids1000_cosebis_contract import build_cosebis_contract
    from scripts.build_kids1000_janus_holst_distance_kernel_audit import (
        kernel_variant_options,
        shape_for_kernel_variant,
    )
    from scripts.build_kids1000_janus_holst_shape_chi2 import best_amplitude, scale_cut_indices, slice_contract
    from scripts.build_kids1000_janus_holst_weyl_cosebis import extract_rows
except ModuleNotFoundError:
    from build_kids1000_cosebis_contract import build_cosebis_contract
    from build_kids1000_janus_holst_distance_kernel_audit import kernel_variant_options, shape_for_kernel_variant
    from build_kids1000_janus_holst_shape_chi2 import best_amplitude, scale_cut_indices, slice_contract
    from build_kids1000_janus_holst_weyl_cosebis import extract_rows


REPORT_PATH = Path("outputs/reports/kids1000_janus_holst_per_bin_nz_shift_audit.md")
JSON_PATH = Path("outputs/reports/kids1000_janus_holst_per_bin_nz_shift_audit.json")


def shift_grid() -> list[float]:
    return [-0.10, -0.05, 0.0, 0.05, 0.10, 0.15, 0.20]


def angular_lens_variant() -> dict:
    return next(variant for variant in kernel_variant_options() if variant["name"] == "angular_lens")


def shifted_single_bin_rows(nz_rows: list[dict], bin_index: int, delta_z: float) -> list[dict]:
    shifted = []
    for row in nz_rows:
        item = dict(row)
        source_z = max(1.0e-4, float(row["Z_MID"]) + delta_z)
        item[f"Z_MID_BIN{bin_index}"] = source_z
        shifted.append(item)
    return shifted


def shape_for_single_bin_shift(bin_index: int, delta_z: float, en_rows: list[dict], nz_rows: list[dict]) -> np.ndarray:
    shifted = shifted_single_bin_rows(nz_rows, bin_index, delta_z)
    return shape_for_kernel_variant(angular_lens_variant(), en_rows, shifted)


def build_payload(bins: list[int] | None = None, shifts: list[float] | None = None) -> dict:
    contract = build_cosebis_contract()
    en_rows, nz_rows = extract_rows()
    observed, covariance = slice_contract(contract, scale_cut_indices())
    bins_to_scan = bins or list(range(1, 6))
    shifts_to_scan = shifts or shift_grid()
    rows = []
    for bin_index in bins_to_scan:
        for delta_z in shifts_to_scan:
            shape = shape_for_single_bin_shift(bin_index, delta_z, en_rows, nz_rows)
            amplitude, chi2 = best_amplitude(observed, shape, covariance)
            rows.append(
                {
                    "shifted_bin": bin_index,
                    "delta_z": delta_z,
                    "best_amplitude": amplitude,
                    "chi2": chi2,
                    "dof": int(observed.size - 1),
                    "chi2_per_dof": chi2 / (observed.size - 1),
                }
            )
    best_by_bin = []
    for bin_index in bins_to_scan:
        candidates = [row for row in rows if row["shifted_bin"] == bin_index]
        best_by_bin.append(min(candidates, key=lambda row: row["chi2"]))
    best = min(rows, key=lambda row: row["chi2"])
    return {
        "description": "Per-bin source-redshift shift diagnostic for the frozen KiDS-1000 Janus-Holst angular_lens candidate.",
        "status": "diagnostic-per-bin-nz-shift-audit-computed",
        "kernel_variant": "angular_lens",
        "rows": rows,
        "best_by_bin": best_by_bin,
        "best_shifted_bin": best["shifted_bin"],
        "best_delta_z": best["delta_z"],
        "best_chi2_per_dof": best["chi2_per_dof"],
        "prediction_ready": False,
        "boundary": (
            "This is a post-hoc single-bin redshift-shift diagnostic using synthetic Z_MID_BIN keys. "
            "It must not be interpreted as a KiDS photo-z nuisance fit."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# KiDS-1000 Janus-Holst Per-Bin n(z) Shift Audit",
        "",
        payload["description"],
        "",
        f"Status: `{payload['status']}`",
        f"Kernel variant: `{payload['kernel_variant']}`",
        f"Best shifted bin: `{payload['best_shifted_bin']}`",
        f"Best delta_z: `{payload['best_delta_z']}`",
        f"Best chi2/dof: `{payload['best_chi2_per_dof']:.6g}`",
        f"Prediction ready: `{payload['prediction_ready']}`",
        "",
        "| shifted bin | best delta_z | chi2/dof |",
        "|---:|---:|---:|",
    ]
    for row in payload["best_by_bin"]:
        lines.append(f"| {row['shifted_bin']} | {row['delta_z']:.6g} | {row['chi2_per_dof']:.6g} |")
    lines.extend(["", payload["boundary"], ""])
    return "\n".join(lines)


def write_reports(report_path: Path = REPORT_PATH, json_path: Path = JSON_PATH) -> dict:
    report_path.parent.mkdir(parents=True, exist_ok=True)
    payload = build_payload()
    json_path.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    report_path.write_text(render_markdown(payload), encoding="utf-8")
    return payload


def main() -> None:
    write_reports()
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {JSON_PATH}")


if __name__ == "__main__":
    main()
