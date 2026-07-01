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
    from scripts.build_kids1000_janus_holst_shape_chi2 import (
        best_amplitude,
        pair_chi2_blocks,
        residual_rows,
        scale_cut_indices,
        slice_contract,
        tomographic_max_bin_scan,
    )
    from scripts.build_kids1000_janus_holst_weyl_cosebis import extract_rows
except ModuleNotFoundError:
    from build_kids1000_cosebis_contract import build_cosebis_contract
    from build_kids1000_janus_holst_distance_kernel_audit import kernel_variant_options, shape_for_kernel_variant
    from build_kids1000_janus_holst_shape_chi2 import (
        best_amplitude,
        pair_chi2_blocks,
        residual_rows,
        scale_cut_indices,
        slice_contract,
        tomographic_max_bin_scan,
    )
    from build_kids1000_janus_holst_weyl_cosebis import extract_rows


REPORT_PATH = Path("outputs/reports/kids1000_janus_holst_kernel_residual_audit.md")
JSON_PATH = Path("outputs/reports/kids1000_janus_holst_kernel_residual_audit.json")


def normalized_en_rows(en_rows: list[dict]) -> list[dict]:
    return [
        {"bin1": int(row["BIN1"]), "bin2": int(row["BIN2"]), "angbin": int(row["ANGBIN"])}
        for row in en_rows
    ]


def build_variant_payload(
    variant: dict,
    rows: list[dict],
    en_rows: list[dict],
    nz_rows: list[dict],
    observed: np.ndarray,
    covariance: np.ndarray,
) -> dict:
    shape = shape_for_kernel_variant(variant, en_rows, nz_rows)
    amplitude, chi2 = best_amplitude(observed, shape, covariance)
    residuals = amplitude * shape - observed
    pulls = residual_rows(rows, observed, covariance, shape, amplitude)
    return {
        "kernel_variant": variant["name"],
        "distance_kernel": variant["distance_kernel"],
        "projection_power": variant["projection_power"],
        "best_amplitude": amplitude,
        "chi2": chi2,
        "dof": int(observed.size - 1),
        "chi2_per_dof": chi2 / (observed.size - 1),
        "worst_diag_pulls": sorted(pulls, key=lambda row: abs(row["pull_diag"]), reverse=True)[:5],
        "pair_chi2_blocks": pair_chi2_blocks(rows, residuals, covariance),
        "tomographic_max_bin_scan": tomographic_max_bin_scan(rows, observed, covariance, shape),
    }


def build_payload() -> dict:
    contract = build_cosebis_contract()
    en_rows, nz_rows = extract_rows()
    observed, covariance = slice_contract(contract, scale_cut_indices())
    rows = normalized_en_rows(en_rows)
    variants = [
        build_variant_payload(variant, rows, en_rows, nz_rows, observed, covariance)
        for variant in kernel_variant_options()
    ]
    best = min(variants, key=lambda row: row["chi2"])
    return {
        "description": "Residual localization for named KiDS-1000 Janus-Holst kernel variants.",
        "status": "diagnostic-kernel-residual-audit-computed",
        "dimension": int(observed.size),
        "variants": variants,
        "best_kernel_variant": best["kernel_variant"],
        "best_chi2_per_dof": best["chi2_per_dof"],
        "prediction_ready": False,
        "boundary": (
            "This localizes residuals after KiDS-inspected eta/tilt and fitted amplitude. "
            "It is not a prediction or a nuisance-parameter closure."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# KiDS-1000 Janus-Holst Kernel Residual Audit",
        "",
        payload["description"],
        "",
        f"Status: `{payload['status']}`",
        f"Dimension: `{payload['dimension']}`",
        f"Best kernel variant: `{payload['best_kernel_variant']}`",
        f"Best chi2/dof: `{payload['best_chi2_per_dof']:.6g}`",
        f"Prediction ready: `{payload['prediction_ready']}`",
        "",
        "## Summary",
        "",
        "| variant | chi2/dof | max-bin-2 chi2/dof | max-bin-5 chi2/dof | worst pair | worst pair chi2/mode |",
        "|---|---:|---:|---:|---|---:|",
    ]
    for variant in payload["variants"]:
        scan = {row["max_bin"]: row for row in variant["tomographic_max_bin_scan"]}
        worst_pair = max(variant["pair_chi2_blocks"], key=lambda row: row["chi2_per_mode"])
        lines.append(
            f"| {variant['kernel_variant']} | {variant['chi2_per_dof']:.6g} | "
            f"{scan[2]['chi2_per_dof']:.6g} | {scan[5]['chi2_per_dof']:.6g} | "
            f"{worst_pair['bin1']}-{worst_pair['bin2']} | {worst_pair['chi2_per_mode']:.6g} |"
        )
    lines.extend(["", "## Best Variant Pair Blocks", ""])
    best = min(payload["variants"], key=lambda row: row["chi2"])
    lines.extend(["| bin1 | bin2 | n | chi2 | chi2/mode |", "|---:|---:|---:|---:|---:|"])
    for row in best["pair_chi2_blocks"]:
        lines.append(
            f"| {row['bin1']} | {row['bin2']} | {row['n']} | "
            f"{row['chi2']:.6g} | {row['chi2_per_mode']:.6g} |"
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
