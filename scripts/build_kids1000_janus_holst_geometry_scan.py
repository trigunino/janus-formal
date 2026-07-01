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
from janus_lab.models import JanusExpansion
from janus_lab.weak_lensing_spectra import janus_xi_curves_for_kids_bins


REPORT_PATH = Path("outputs/reports/kids1000_janus_holst_geometry_scan.md")
JSON_PATH = Path("outputs/reports/kids1000_janus_holst_geometry_scan.json")


def default_q0_grid() -> list[float]:
    return [-0.16, -0.12, -0.087, -0.06, -0.04, -0.02, -0.01]


def max_source_redshift(nz_rows: list[dict]) -> float:
    return max(float(row["Z_MID"]) for row in nz_rows)


def retained_source_fractions(nz_rows: list[dict], z_max: float) -> dict[str, float]:
    z = np.asarray([float(row["Z_MID"]) for row in nz_rows], dtype=float)
    mask = z <= z_max
    fractions = {}
    for index in range(1, 6):
        weights = np.asarray([float(row[f"BIN{index}"]) for row in nz_rows], dtype=float)
        total = float(np.trapezoid(weights, z))
        retained = float(np.trapezoid(weights[mask], z[mask])) if np.count_nonzero(mask) > 1 else 0.0
        fractions[f"bin{index}"] = retained / total if total > 0.0 else float("nan")
    return fractions


def shape_for_q0(q0: float, en_rows: list[dict], nz_rows: list[dict]) -> np.ndarray:
    theta_arcmin = np.geomspace(0.5, 300.0, 256)
    _constants, power = janus_holst_weyl_power_factory(eta_holst=0.0, spectral_index=0.5)
    xi_plus, xi_minus = janus_xi_curves_for_kids_bins(
        nz_rows,
        theta_arcmin,
        q0=q0,
        weyl_power=power,
    )
    return np.asarray(cosebis_vector_from_xi(theta_arcmin, xi_plus, xi_minus, en_rows, n_max=5), dtype=float)


def build_payload(q0_grid: list[float] | None = None) -> dict:
    contract = build_cosebis_contract()
    en_rows, nz_rows = extract_rows()
    observed, covariance = slice_contract(contract, scale_cut_indices())
    source_z_max = max_source_redshift(nz_rows)
    rows = []
    for q0 in q0_grid or default_q0_grid():
        model = JanusExpansion.from_q0(float(q0))
        fractions = retained_source_fractions(nz_rows, model.z_max)
        shape = shape_for_q0(float(q0), en_rows, nz_rows)
        amplitude, chi2 = best_amplitude(observed, shape, covariance)
        chi2_per_dof = chi2 / (observed.size - 1)
        rows.append(
            {
                "q0": float(q0),
                "z_max": float(model.z_max),
                "min_retained_source_fraction": min(fractions.values()),
                "retained_source_fractions": fractions,
                "best_amplitude": amplitude,
                "chi2": chi2,
                "dof": int(observed.size - 1),
                "chi2_per_dof": chi2_per_dof,
            }
        )
    best = min(rows, key=lambda row: row["chi2"])
    return {
        "description": "Diagnostic Janus q0 geometry scan for KiDS-1000 at eta_holst=0 and spectral_index=0.5.",
        "status": "diagnostic-geometry-scan-computed",
        "dimension": int(observed.size),
        "kids_source_z_max": source_z_max,
        "rows": rows,
        "best_q0": best["q0"],
        "best_chi2_per_dof": best["chi2_per_dof"],
        "prediction_ready": False,
        "boundary": (
            "This scans the Janus distance-kernel parameter after inspecting KiDS and refits "
            "amplitude. It diagnoses geometry tension; it is not a DESI/SN-validated q0 update."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# KiDS-1000 Janus-Holst Geometry Scan",
        "",
        payload["description"],
        "",
        f"Status: `{payload['status']}`",
        f"Dimension: `{payload['dimension']}`",
        f"KiDS source z max: `{payload['kids_source_z_max']:.6g}`",
        f"Best q0: `{payload['best_q0']}`",
        f"Best chi2/dof: `{payload['best_chi2_per_dof']:.6g}`",
        f"Prediction ready: `{payload['prediction_ready']}`",
        "",
        "| q0 | z_max | min source retained | best amplitude | chi2 | dof | chi2/dof |",
        "|---:|---:|---:|---:|---:|---:|---:|",
    ]
    for row in payload["rows"]:
        lines.append(
            f"| {row['q0']:.6g} | {row['z_max']:.6g} | {row['min_retained_source_fraction']:.6g} | "
            f"{row['best_amplitude']:.6g} | {row['chi2']:.6g} | {row['dof']} | {row['chi2_per_dof']:.6g} |"
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
