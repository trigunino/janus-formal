from __future__ import annotations

from pathlib import Path
import json

import numpy as np

try:
    from scripts.build_kids1000_cosebis_contract import build_cosebis_contract
    from scripts.build_kids1000_janus_holst_shape_chi2 import best_amplitude, scale_cut_indices, slice_contract
    from scripts.build_kids1000_janus_holst_weyl_cosebis import (
        extract_rows,
        janus_holst_weyl_power_factory,
    )
except ModuleNotFoundError:
    from build_kids1000_cosebis_contract import build_cosebis_contract
    from build_kids1000_janus_holst_shape_chi2 import best_amplitude, scale_cut_indices, slice_contract
    from build_kids1000_janus_holst_weyl_cosebis import extract_rows, janus_holst_weyl_power_factory

from janus_lab.cosebis import cosebis_vector_from_xi
from janus_lab.weak_lensing_spectra import janus_xi_curves_for_kids_bins


REPORT_PATH = Path("outputs/reports/kids1000_janus_holst_redshift_kernel_scan.md")
JSON_PATH = Path("outputs/reports/kids1000_janus_holst_redshift_kernel_scan.json")


def default_kernel_power_grid() -> list[float]:
    return [-8.0, -6.0, -4.0, -3.0, -2.0, -1.0, 0.0, 1.0, 2.0, 3.0]


def redshift_projection_factor(redshift_power: float):
    def factor(z: np.ndarray) -> np.ndarray:
        return (1.0 + np.asarray(z, dtype=float)) ** redshift_power

    return factor


def shape_for_kernel_power(redshift_power: float, en_rows: list[dict], nz_rows: list[dict]) -> np.ndarray:
    theta_arcmin = np.geomspace(0.5, 300.0, 256)
    _constants, power = janus_holst_weyl_power_factory(eta_holst=0.0, spectral_index=0.5)
    xi_plus, xi_minus = janus_xi_curves_for_kids_bins(
        nz_rows,
        theta_arcmin,
        weyl_power=power,
        projection_factor=redshift_projection_factor(redshift_power),
    )
    return np.asarray(cosebis_vector_from_xi(theta_arcmin, xi_plus, xi_minus, en_rows, n_max=5), dtype=float)


def build_payload(kernel_power_grid: list[float] | None = None) -> dict:
    contract = build_cosebis_contract()
    en_rows, nz_rows = extract_rows()
    observed, covariance = slice_contract(contract, scale_cut_indices())
    rows = []
    for redshift_power in kernel_power_grid or default_kernel_power_grid():
        shape = shape_for_kernel_power(float(redshift_power), en_rows, nz_rows)
        amplitude, chi2 = best_amplitude(observed, shape, covariance)
        rows.append(
            {
                "eta_holst": 0.0,
                "spectral_index": 0.5,
                "redshift_kernel_power": float(redshift_power),
                "best_amplitude": amplitude,
                "chi2": chi2,
                "dof": int(observed.size - 1),
                "chi2_per_dof": chi2 / (observed.size - 1),
            }
        )
    best = min(rows, key=lambda row: row["chi2"])
    return {
        "description": "Diagnostic Limber projection-factor scan for KiDS-1000 at eta_holst=0 and spectral_index=0.5.",
        "status": "diagnostic-redshift-kernel-scan-computed",
        "dimension": int(observed.size),
        "rows": rows,
        "best_redshift_kernel_power": best["redshift_kernel_power"],
        "best_chi2_per_dof": best["chi2_per_dof"],
        "prediction_ready": False,
        "boundary": (
            "This multiplies the Limber integrand by a post-hoc `(1+z)^p` factor and refits "
            "amplitude. It diagnoses missing projection/growth terms, not a closed kernel."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# KiDS-1000 Janus-Holst Redshift-Kernel Scan",
        "",
        payload["description"],
        "",
        f"Status: `{payload['status']}`",
        f"Dimension: `{payload['dimension']}`",
        f"Best redshift kernel power: `{payload['best_redshift_kernel_power']}`",
        f"Best chi2/dof: `{payload['best_chi2_per_dof']:.6g}`",
        f"Prediction ready: `{payload['prediction_ready']}`",
        "",
        "| redshift power | best amplitude | chi2 | dof | chi2/dof |",
        "|---:|---:|---:|---:|---:|",
    ]
    for row in payload["rows"]:
        lines.append(
            f"| {row['redshift_kernel_power']:.6g} | {row['best_amplitude']:.6g} | "
            f"{row['chi2']:.6g} | {row['dof']} | {row['chi2_per_dof']:.6g} |"
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
