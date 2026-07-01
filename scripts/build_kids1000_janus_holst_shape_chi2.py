from __future__ import annotations

from pathlib import Path
import csv
import json

import numpy as np

try:
    from scripts.build_kids1000_cosebis_contract import build_cosebis_contract
    from scripts.build_kids1000_janus_holst_weyl_cosebis import build_payload as build_holst_payload
except ModuleNotFoundError:
    from build_kids1000_cosebis_contract import build_cosebis_contract
    from build_kids1000_janus_holst_weyl_cosebis import build_payload as build_holst_payload

from janus_lab.statistics import fixed_prediction_chi_square, weighted_linear_fit


REPORT_PATH = Path("outputs/reports/kids1000_janus_holst_shape_chi2.md")
JSON_PATH = Path("outputs/reports/kids1000_janus_holst_shape_chi2.json")
CSV_PATH = Path("outputs/reports/kids1000_janus_holst_shape_residuals.csv")


def scale_cut_indices(total_modes_per_pair: int = 20, kept_modes: int = 5, pair_count: int = 15) -> list[int]:
    return [
        pair_index * total_modes_per_pair + mode_index
        for pair_index in range(pair_count)
        for mode_index in range(kept_modes)
    ]


def slice_contract(contract: dict, indices: list[int]) -> tuple[np.ndarray, np.ndarray]:
    observed = np.asarray(contract["observed_vector"], dtype=float)[indices]
    covariance = np.asarray(contract["covariance"], dtype=float)[np.ix_(indices, indices)]
    return observed, covariance


def best_amplitude(observed: np.ndarray, shape: np.ndarray, covariance: np.ndarray) -> tuple[float, float]:
    coeffs, _prediction, chi2 = weighted_linear_fit(shape[:, np.newaxis], observed, covariance)
    return float(coeffs[0]), float(chi2)


def residual_rows(holst_rows: list[dict], observed: np.ndarray, covariance: np.ndarray, shape: np.ndarray, amplitude: float) -> list[dict]:
    prediction = amplitude * shape
    sigma = np.sqrt(np.diag(covariance))
    rows = []
    for index, (row, obs, pred, sig) in enumerate(zip(holst_rows, observed, prediction, sigma)):
        residual = float(pred - obs)
        rows.append(
            {
                "index": index,
                "bin1": int(row["bin1"]),
                "bin2": int(row["bin2"]),
                "angbin": int(row["angbin"]),
                "observed": float(obs),
                "prediction_best_amp": float(pred),
                "shape": float(shape[index]),
                "sigma_diag": float(sig),
                "residual": residual,
                "pull_diag": residual / float(sig) if sig > 0 else float("nan"),
            }
        )
    return rows


def pair_chi2_blocks(rows: list[dict], residuals: np.ndarray, covariance: np.ndarray) -> list[dict]:
    blocks = []
    for pair in sorted({(row["bin1"], row["bin2"]) for row in rows}):
        indices = [index for index, row in enumerate(rows) if (row["bin1"], row["bin2"]) == pair]
        sub_residuals = residuals[indices]
        sub_covariance = covariance[np.ix_(indices, indices)]
        chi2 = float(sub_residuals @ np.linalg.solve(sub_covariance, sub_residuals))
        blocks.append(
            {
                "bin1": pair[0],
                "bin2": pair[1],
                "n": len(indices),
                "chi2": chi2,
                "chi2_per_mode": chi2 / len(indices),
            }
        )
    return blocks


def tomographic_max_bin_scan(rows: list[dict], observed: np.ndarray, covariance: np.ndarray, shape: np.ndarray) -> list[dict]:
    scan = []
    for max_bin in range(1, 6):
        indices = [
            index
            for index, row in enumerate(rows)
            if int(row["bin1"]) <= max_bin and int(row["bin2"]) <= max_bin
        ]
        if not indices:
            continue
        sub_observed = observed[indices]
        sub_shape = shape[indices]
        sub_covariance = covariance[np.ix_(indices, indices)]
        amplitude, chi2 = best_amplitude(sub_observed, sub_shape, sub_covariance)
        scan.append(
            {
                "max_bin": max_bin,
                "n": len(indices),
                "best_amplitude": amplitude,
                "chi2": chi2,
                "dof": len(indices) - 1,
                "chi2_per_dof": chi2 / (len(indices) - 1) if len(indices) > 1 else float("nan"),
            }
        )
    return scan


def build_payload() -> dict:
    contract = build_cosebis_contract()
    holst = build_holst_payload()
    indices = scale_cut_indices()
    observed, covariance = slice_contract(contract, indices)
    shape = np.asarray([row["janus_holst_cosebis_en"] for row in holst["rows"]], dtype=float)
    unit = fixed_prediction_chi_square(
        "kids1000_janus_holst_unit_shape",
        observed,
        shape,
        covariance,
    )
    amplitude, chi2_best = best_amplitude(observed, shape, covariance)
    residuals_best = amplitude * shape - observed
    residual_table = residual_rows(holst["rows"], observed, covariance, shape, amplitude)
    worst_pulls = sorted(residual_table, key=lambda row: abs(row["pull_diag"]), reverse=True)[:10]
    pair_blocks = pair_chi2_blocks(holst["rows"], residuals_best, covariance)
    max_bin_scan = tomographic_max_bin_scan(holst["rows"], observed, covariance, shape)
    gates = {
        "kids_scale_cut_covariance_sliced": True,
        "cosebis_operator_ready": True,
        "janus_holst_weyl_shape_ready": True,
        "primordial_amplitude_source_derived": False,
        "value_slip_green_kernel_closed": False,
        "nonlinear_small_scale_closure_ready": False,
        "intrinsic_alignment_policy_fixed": False,
        "baryon_feedback_policy_fixed": False,
    }
    return {
        "description": "KiDS-1000 diagnostic chi2 for the Janus-Holst COSEBIs shape.",
        "status": "diagnostic-shape-chi2-computed",
        "dimension": int(observed.size),
        "prediction_vector_id": holst["status"],
        "unit_amplitude": {
            "chi2": unit.chi2,
            "dof": unit.dof,
            "chi2_per_dof": unit.chi2_per_dof,
        },
        "best_single_amplitude_diagnostic": {
            "amplitude": amplitude,
            "chi2": chi2_best,
            "dof": int(observed.size - 1),
            "chi2_per_dof": chi2_best / (observed.size - 1),
        },
        "residuals_csv": str(CSV_PATH),
        "residual_rows": residual_table,
        "worst_diag_pulls": worst_pulls,
        "pair_chi2_blocks": pair_blocks,
        "tomographic_max_bin_scan": max_bin_scan,
        "gates": gates,
        "prediction_ready": all(gates.values()),
        "chi2_claim_ready": False,
        "boundary": (
            "This is a diagnostic shape comparison. The best-amplitude row fits one scalar "
            "to KiDS and is not a Janus prediction. A prediction claim requires closing the "
            "amplitude, value-slip, nonlinear, IA and baryon gates before inspecting residuals."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# KiDS-1000 Janus-Holst Shape Chi2",
        "",
        payload["description"],
        "",
        f"Status: `{payload['status']}`",
        f"Dimension: `{payload['dimension']}`",
        f"Prediction ready: `{payload['prediction_ready']}`",
        f"Chi2 claim ready: `{payload['chi2_claim_ready']}`",
        "",
        "## Scores",
        "",
        f"- unit amplitude chi2/dof: `{payload['unit_amplitude']['chi2']:.6g}` / `{payload['unit_amplitude']['dof']}` = `{payload['unit_amplitude']['chi2_per_dof']:.6g}`",
        f"- best amplitude diagnostic: `{payload['best_single_amplitude_diagnostic']['amplitude']:.6g}`",
        f"- best amplitude chi2/dof: `{payload['best_single_amplitude_diagnostic']['chi2']:.6g}` / `{payload['best_single_amplitude_diagnostic']['dof']}` = `{payload['best_single_amplitude_diagnostic']['chi2_per_dof']:.6g}`",
        f"- residuals CSV: `{payload['residuals_csv']}`",
        "",
        "## Worst Diagonal Pulls",
        "",
        "| bin1 | bin2 | mode | observed | prediction | pull diag |",
        "|---:|---:|---:|---:|---:|---:|",
    ]
    for row in payload["worst_diag_pulls"]:
        lines.append(
            f"| {row['bin1']} | {row['bin2']} | {row['angbin']} | "
            f"{row['observed']:.6g} | {row['prediction_best_amp']:.6g} | {row['pull_diag']:.3g} |"
        )
    lines.extend(
        [
            "",
            "## Pair Blocks",
            "",
            "| bin1 | bin2 | n | chi2 | chi2/mode |",
            "|---:|---:|---:|---:|---:|",
        ]
    )
    for row in payload["pair_chi2_blocks"]:
        lines.append(
            f"| {row['bin1']} | {row['bin2']} | {row['n']} | "
            f"{row['chi2']:.6g} | {row['chi2_per_mode']:.6g} |"
        )
    lines.extend(
        [
            "",
            "## Tomographic Max-Bin Scan",
            "",
            "| max bin | n | best amplitude | chi2 | chi2/dof |",
            "|---:|---:|---:|---:|---:|",
        ]
    )
    for row in payload["tomographic_max_bin_scan"]:
        lines.append(
            f"| {row['max_bin']} | {row['n']} | {row['best_amplitude']:.6g} | "
            f"{row['chi2']:.6g} | {row['chi2_per_dof']:.6g} |"
        )
    lines.extend(
        [
        "",
        "## Gates",
        ]
    )
    lines.extend(f"- {key}: `{value}`" for key, value in payload["gates"].items())
    lines.extend(["", payload["boundary"], ""])
    return "\n".join(lines)


def write_reports(report_path: Path = REPORT_PATH, json_path: Path = JSON_PATH) -> dict:
    report_path.parent.mkdir(parents=True, exist_ok=True)
    payload = build_payload()
    json_path.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    with CSV_PATH.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(payload["residual_rows"][0].keys()))
        writer.writeheader()
        writer.writerows(payload["residual_rows"])
    report_path.write_text(render_markdown(payload), encoding="utf-8")
    return payload


def main() -> None:
    write_reports()
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {JSON_PATH}")


if __name__ == "__main__":
    main()
