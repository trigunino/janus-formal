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
    from scripts.build_kids1000_janus_holst_kernel_residual_audit import normalized_en_rows
    from scripts.build_kids1000_janus_holst_shape_chi2 import (
        best_amplitude,
        pair_chi2_blocks,
        residual_rows,
        scale_cut_indices,
        slice_contract,
    )
    from scripts.build_kids1000_janus_holst_weyl_cosebis import extract_rows
except ModuleNotFoundError:
    from build_kids1000_cosebis_contract import build_cosebis_contract
    from build_kids1000_janus_holst_distance_kernel_audit import kernel_variant_options, shape_for_kernel_variant
    from build_kids1000_janus_holst_kernel_residual_audit import normalized_en_rows
    from build_kids1000_janus_holst_shape_chi2 import (
        best_amplitude,
        pair_chi2_blocks,
        residual_rows,
        scale_cut_indices,
        slice_contract,
    )
    from build_kids1000_janus_holst_weyl_cosebis import extract_rows


REPORT_PATH = Path("outputs/reports/kids1000_janus_holst_pair23_audit.md")
JSON_PATH = Path("outputs/reports/kids1000_janus_holst_pair23_audit.json")


def normalized_bin_distribution(nz_rows: list[dict], bin_index: int) -> tuple[np.ndarray, np.ndarray]:
    z = np.asarray([float(row["Z_MID"]) for row in nz_rows], dtype=float)
    weights = np.asarray([float(row[f"BIN{bin_index}"]) for row in nz_rows], dtype=float)
    total = float(np.trapezoid(weights, z))
    if total <= 0.0:
        raise ValueError("source bin has zero n(z) weight")
    return z, weights / total


def source_bin_stats(nz_rows: list[dict], bin_index: int) -> dict:
    z, weights = normalized_bin_distribution(nz_rows, bin_index)
    mean = float(np.trapezoid(z * weights, z))
    variance = float(np.trapezoid((z - mean) ** 2 * weights, z))
    return {
        "bin": bin_index,
        "z_mean": mean,
        "z_std": float(np.sqrt(max(variance, 0.0))),
        "z_peak": float(z[int(np.argmax(weights))]),
    }


def source_overlap(nz_rows: list[dict], bin_i: int, bin_j: int) -> float:
    z_i, weights_i = normalized_bin_distribution(nz_rows, bin_i)
    z_j, weights_j = normalized_bin_distribution(nz_rows, bin_j)
    if not np.allclose(z_i, z_j):
        raise ValueError("source bins must share the same redshift grid")
    return float(np.trapezoid(np.minimum(weights_i, weights_j), z_i))


def best_variant() -> dict:
    return next(variant for variant in kernel_variant_options() if variant["name"] == "angular_lens")


def build_payload() -> dict:
    contract = build_cosebis_contract()
    en_rows, nz_rows = extract_rows()
    rows = normalized_en_rows(en_rows)
    observed, covariance = slice_contract(contract, scale_cut_indices())
    variant = best_variant()
    shape = shape_for_kernel_variant(variant, en_rows, nz_rows)
    amplitude, chi2 = best_amplitude(observed, shape, covariance)
    residuals = amplitude * shape - observed
    pulls = residual_rows(rows, observed, covariance, shape, amplitude)
    pair_blocks = pair_chi2_blocks(rows, residuals, covariance)
    pair23_rows = [row for row in pulls if row["bin1"] == 2 and row["bin2"] == 3]
    pair23_block = next(row for row in pair_blocks if row["bin1"] == 2 and row["bin2"] == 3)
    return {
        "description": "Focused audit of the dominant KiDS-1000 Janus-Holst residual pair 2-3.",
        "status": "diagnostic-pair23-audit-computed",
        "kernel_variant": variant["name"],
        "dimension": int(observed.size),
        "global_chi2_per_dof": chi2 / (observed.size - 1),
        "pair23_block": pair23_block,
        "pair23_rows": pair23_rows,
        "bin2_stats": source_bin_stats(nz_rows, 2),
        "bin3_stats": source_bin_stats(nz_rows, 3),
        "bin23_source_overlap": source_overlap(nz_rows, 2, 3),
        "prediction_ready": False,
        "boundary": (
            "This audits the worst pair after the diagnostic candidate is frozen. It does not "
            "introduce a pair-specific correction or fit."
        ),
    }


def render_markdown(payload: dict) -> str:
    block = payload["pair23_block"]
    lines = [
        "# KiDS-1000 Janus-Holst Pair 2-3 Audit",
        "",
        payload["description"],
        "",
        f"Status: `{payload['status']}`",
        f"Kernel variant: `{payload['kernel_variant']}`",
        f"Global chi2/dof: `{payload['global_chi2_per_dof']:.6g}`",
        f"Pair 2-3 chi2/mode: `{block['chi2_per_mode']:.6g}`",
        f"Bin 2 z_mean: `{payload['bin2_stats']['z_mean']:.6g}`",
        f"Bin 3 z_mean: `{payload['bin3_stats']['z_mean']:.6g}`",
        f"Bin 2-3 source overlap: `{payload['bin23_source_overlap']:.6g}`",
        f"Prediction ready: `{payload['prediction_ready']}`",
        "",
        "| mode | observed | prediction | residual | pull diag |",
        "|---:|---:|---:|---:|---:|",
    ]
    for row in payload["pair23_rows"]:
        lines.append(
            f"| {row['angbin']} | {row['observed']:.6g} | {row['prediction_best_amp']:.6g} | "
            f"{row['residual']:.6g} | {row['pull_diag']:.6g} |"
        )
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
