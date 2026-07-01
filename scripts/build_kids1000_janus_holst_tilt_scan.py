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


REPORT_PATH = Path("outputs/reports/kids1000_janus_holst_tilt_scan.md")
JSON_PATH = Path("outputs/reports/kids1000_janus_holst_tilt_scan.json")


def default_tilt_grid() -> list[float]:
    return [-1.0, -0.5, 0.0, 0.25, 0.5, 0.75, 1.0, 1.5, 2.0]


def shape_for_tilt(spectral_index: float, en_rows: list[dict], nz_rows: list[dict]) -> np.ndarray:
    theta_arcmin = np.geomspace(0.5, 300.0, 256)
    _constants, power = janus_holst_weyl_power_factory(eta_holst=0.0, spectral_index=spectral_index)
    xi_plus, xi_minus = janus_xi_curves_for_kids_bins(nz_rows, theta_arcmin, weyl_power=power)
    return np.asarray(cosebis_vector_from_xi(theta_arcmin, xi_plus, xi_minus, en_rows, n_max=5), dtype=float)


def build_payload(tilt_grid: list[float] | None = None) -> dict:
    contract = build_cosebis_contract()
    en_rows, nz_rows = extract_rows()
    observed, covariance = slice_contract(contract, scale_cut_indices())
    rows = []
    for tilt in tilt_grid or default_tilt_grid():
        shape = shape_for_tilt(float(tilt), en_rows, nz_rows)
        amplitude, chi2 = best_amplitude(observed, shape, covariance)
        rows.append(
            {
                "eta_holst": 0.0,
                "spectral_index": float(tilt),
                "best_amplitude": amplitude,
                "chi2": chi2,
                "dof": int(observed.size - 1),
                "chi2_per_dof": chi2 / (observed.size - 1),
            }
        )
    best = min(rows, key=lambda row: row["chi2"])
    return {
        "description": "Diagnostic Weyl spectral-tilt scan at eta_holst=0 for KiDS-1000.",
        "status": "diagnostic-tilt-scan-computed",
        "dimension": int(observed.size),
        "rows": rows,
        "best_spectral_index": best["spectral_index"],
        "best_chi2_per_dof": best["chi2_per_dof"],
        "prediction_ready": False,
        "boundary": (
            "The spectral tilt is scanned after seeing KiDS and amplitude is refitted. "
            "This is a missing-transfer/nonlinear diagnostic, not a primordial prediction."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# KiDS-1000 Janus-Holst Tilt Scan",
        "",
        payload["description"],
        "",
        f"Status: `{payload['status']}`",
        f"Dimension: `{payload['dimension']}`",
        f"Best spectral index: `{payload['best_spectral_index']}`",
        f"Best chi2/dof: `{payload['best_chi2_per_dof']:.6g}`",
        f"Prediction ready: `{payload['prediction_ready']}`",
        "",
        "| spectral index | best amplitude | chi2 | dof | chi2/dof |",
        "|---:|---:|---:|---:|---:|",
    ]
    for row in payload["rows"]:
        lines.append(
            f"| {row['spectral_index']:.6g} | {row['best_amplitude']:.6g} | "
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
