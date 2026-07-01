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
    from scripts.build_kids1000_janus_holst_shape_chi2 import best_amplitude, scale_cut_indices, slice_contract
    from scripts.build_kids1000_janus_holst_weyl_cosebis import extract_rows
except ModuleNotFoundError:
    from build_kids1000_cosebis_contract import build_cosebis_contract
    from build_kids1000_janus_holst_distance_kernel_audit import kernel_variant_options, shape_for_kernel_variant
    from build_kids1000_janus_holst_kernel_residual_audit import normalized_en_rows
    from build_kids1000_janus_holst_shape_chi2 import best_amplitude, scale_cut_indices, slice_contract
    from build_kids1000_janus_holst_weyl_cosebis import extract_rows


REPORT_PATH = Path("outputs/reports/kids1000_janus_holst_pair_amplitude_audit.md")
JSON_PATH = Path("outputs/reports/kids1000_janus_holst_pair_amplitude_audit.json")


def angular_lens_variant() -> dict:
    return next(variant for variant in kernel_variant_options() if variant["name"] == "angular_lens")


def pair_amplitude_rows(rows: list[dict], observed: np.ndarray, covariance: np.ndarray, shape: np.ndarray) -> list[dict]:
    global_amp, _global_chi2 = best_amplitude(observed, shape, covariance)
    output = []
    for pair in sorted({(row["bin1"], row["bin2"]) for row in rows}):
        indices = [index for index, row in enumerate(rows) if (row["bin1"], row["bin2"]) == pair]
        sub_observed = observed[indices]
        sub_shape = shape[indices]
        sub_covariance = covariance[np.ix_(indices, indices)]
        amplitude, chi2 = best_amplitude(sub_observed, sub_shape, sub_covariance)
        output.append(
            {
                "bin1": pair[0],
                "bin2": pair[1],
                "n": len(indices),
                "pair_best_amplitude": amplitude,
                "pair_to_global_amplitude_ratio": amplitude / global_amp if global_amp else float("nan"),
                "pair_fit_chi2": chi2,
                "pair_fit_dof": len(indices) - 1,
                "pair_fit_chi2_per_dof": chi2 / (len(indices) - 1),
            }
        )
    return output


def build_payload() -> dict:
    contract = build_cosebis_contract()
    en_rows, nz_rows = extract_rows()
    rows = normalized_en_rows(en_rows)
    observed, covariance = slice_contract(contract, scale_cut_indices())
    shape = shape_for_kernel_variant(angular_lens_variant(), en_rows, nz_rows)
    global_amp, global_chi2 = best_amplitude(observed, shape, covariance)
    pair_rows = pair_amplitude_rows(rows, observed, covariance, shape)
    pair23 = next(row for row in pair_rows if row["bin1"] == 2 and row["bin2"] == 3)
    return {
        "description": "Per-pair amplitude diagnostic for the KiDS-1000 Janus-Holst angular_lens candidate.",
        "status": "diagnostic-pair-amplitude-audit-computed",
        "kernel_variant": "angular_lens",
        "global_best_amplitude": global_amp,
        "global_chi2_per_dof": global_chi2 / (observed.size - 1),
        "pair_rows": pair_rows,
        "pair23_ratio": pair23["pair_to_global_amplitude_ratio"],
        "prediction_ready": False,
        "boundary": (
            "Per-pair amplitudes are fitted after inspecting KiDS and are diagnostic only. "
            "They identify tomography normalization failures; they are not nuisance closures."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# KiDS-1000 Janus-Holst Pair-Amplitude Audit",
        "",
        payload["description"],
        "",
        f"Status: `{payload['status']}`",
        f"Kernel variant: `{payload['kernel_variant']}`",
        f"Global chi2/dof: `{payload['global_chi2_per_dof']:.6g}`",
        f"Pair 2-3 amplitude/global ratio: `{payload['pair23_ratio']:.6g}`",
        f"Prediction ready: `{payload['prediction_ready']}`",
        "",
        "| bin1 | bin2 | amp/global | pair-fit chi2/dof |",
        "|---:|---:|---:|---:|",
    ]
    for row in payload["pair_rows"]:
        lines.append(
            f"| {row['bin1']} | {row['bin2']} | {row['pair_to_global_amplitude_ratio']:.6g} | "
            f"{row['pair_fit_chi2_per_dof']:.6g} |"
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
