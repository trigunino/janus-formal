from __future__ import annotations

from pathlib import Path
import json

import numpy as np

try:
    from scripts.build_kids1000_cosebis_contract import build_cosebis_contract
    from scripts.build_kids1000_janus_holst_shape_chi2 import (
        best_amplitude,
        pair_chi2_blocks,
        scale_cut_indices,
        slice_contract,
        tomographic_max_bin_scan,
    )
    from scripts.build_kids1000_janus_holst_weyl_cosebis import (
        extract_rows,
        janus_holst_weyl_power_factory,
    )
except ModuleNotFoundError:
    from build_kids1000_cosebis_contract import build_cosebis_contract
    from build_kids1000_janus_holst_shape_chi2 import (
        best_amplitude,
        pair_chi2_blocks,
        scale_cut_indices,
        slice_contract,
        tomographic_max_bin_scan,
    )
    from build_kids1000_janus_holst_weyl_cosebis import extract_rows, janus_holst_weyl_power_factory

from janus_lab.cosebis import cosebis_vector_from_xi
from janus_lab.weak_lensing_spectra import janus_xi_curves_for_kids_bins


REPORT_PATH = Path("outputs/reports/kids1000_janus_holst_eta_scan.md")
JSON_PATH = Path("outputs/reports/kids1000_janus_holst_eta_scan.json")


def default_eta_grid() -> list[float]:
    return [-3.0, -2.0, -1.0, -0.5, -0.25, 0.0, 0.25, 0.5, 1.0, 2.0, 3.0]


def shape_for_eta(eta_holst: float, en_rows: list[dict], nz_rows: list[dict]) -> tuple[dict, np.ndarray]:
    theta_arcmin = np.geomspace(0.5, 300.0, 256)
    constants, power = janus_holst_weyl_power_factory(eta_holst=eta_holst)
    xi_plus, xi_minus = janus_xi_curves_for_kids_bins(nz_rows, theta_arcmin, weyl_power=power)
    return constants, np.asarray(cosebis_vector_from_xi(theta_arcmin, xi_plus, xi_minus, en_rows, n_max=5), dtype=float)


def normalized_rows(en_rows: list[dict]) -> list[dict]:
    return [
        {"bin1": int(row["BIN1"]), "bin2": int(row["BIN2"]), "angbin": int(row["ANGBIN"])}
        for row in en_rows
    ]


def build_payload(eta_grid: list[float] | None = None) -> dict:
    contract = build_cosebis_contract()
    en_rows, nz_rows = extract_rows()
    observed, covariance = slice_contract(contract, scale_cut_indices())
    rows = []
    shapes = {}
    for eta_holst in eta_grid or default_eta_grid():
        constants, shape = shape_for_eta(float(eta_holst), en_rows, nz_rows)
        amplitude, chi2 = best_amplitude(observed, shape, covariance)
        shapes[float(eta_holst)] = shape
        rows.append(
            {
                "eta_holst": float(eta_holst),
                "omega_m0": float(constants["Omega_m0"]),
                "omega_t0": float(constants["Omega_T0"]),
                "best_amplitude": amplitude,
                "chi2": chi2,
                "dof": int(observed.size - 1),
                "chi2_per_dof": chi2 / (observed.size - 1),
            }
        )
    best = min(rows, key=lambda row: row["chi2"])
    best_shape = shapes[best["eta_holst"]]
    best_residuals = best["best_amplitude"] * best_shape - observed
    row_contract = normalized_rows(en_rows)
    return {
        "description": "Diagnostic eta_holst scan for the KiDS-1000 Janus-Holst COSEBIs shape.",
        "status": "diagnostic-eta-scan-computed",
        "dimension": int(observed.size),
        "rows": rows,
        "best_eta_holst": best["eta_holst"],
        "best_chi2_per_dof": best["chi2_per_dof"],
        "best_pair_chi2_blocks": pair_chi2_blocks(row_contract, best_residuals, covariance),
        "best_tomographic_max_bin_scan": tomographic_max_bin_scan(row_contract, observed, covariance, best_shape),
        "prediction_ready": False,
        "boundary": (
            "This inspects eta_holst after seeing KiDS and refits amplitude at every point. "
            "It is a branch diagnostic, not a value-slip Green-kernel closure."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# KiDS-1000 Janus-Holst Eta Scan",
        "",
        payload["description"],
        "",
        f"Status: `{payload['status']}`",
        f"Dimension: `{payload['dimension']}`",
        f"Best eta_holst: `{payload['best_eta_holst']}`",
        f"Best chi2/dof: `{payload['best_chi2_per_dof']:.6g}`",
        f"Prediction ready: `{payload['prediction_ready']}`",
        "",
        "| eta_holst | best amplitude | chi2 | dof | chi2/dof |",
        "|---:|---:|---:|---:|---:|",
    ]
    for row in payload["rows"]:
        lines.append(
            f"| {row['eta_holst']:.6g} | {row['best_amplitude']:.6g} | "
            f"{row['chi2']:.6g} | {row['dof']} | {row['chi2_per_dof']:.6g} |"
        )
    lines.extend(
        [
            "",
            "## Best-Eta Tomographic Scan",
            "",
            "| max bin | n | best amplitude | chi2 | chi2/dof |",
            "|---:|---:|---:|---:|---:|",
        ]
    )
    for row in payload["best_tomographic_max_bin_scan"]:
        lines.append(
            f"| {row['max_bin']} | {row['n']} | {row['best_amplitude']:.6g} | "
            f"{row['chi2']:.6g} | {row['chi2_per_dof']:.6g} |"
        )
    lines.extend(
        [
            "",
            "## Best-Eta Pair Blocks",
            "",
            "| bin1 | bin2 | n | chi2 | chi2/mode |",
            "|---:|---:|---:|---:|---:|",
        ]
    )
    for row in payload["best_pair_chi2_blocks"]:
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
