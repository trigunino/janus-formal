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


REPORT_PATH = Path("outputs/reports/kids1000_janus_holst_distance_kernel_audit.md")
JSON_PATH = Path("outputs/reports/kids1000_janus_holst_distance_kernel_audit.json")


def distance_kernel_options() -> list[str]:
    return [variant["name"] for variant in kernel_variant_options()]


def kernel_variant_options() -> list[dict]:
    return [
        {"name": "comoving", "distance_kernel": "comoving", "projection_power": 0.0},
        {"name": "comoving_standard_jacobi", "distance_kernel": "comoving", "projection_power": 1.0},
        {"name": "angular_lens", "distance_kernel": "angular_lens", "projection_power": 0.0},
        {"name": "angular_lens_standard_jacobi", "distance_kernel": "angular_lens", "projection_power": 1.0},
    ]


def projection_factor_for_power(power: float):
    if power == 0.0:
        return None

    def factor(z: np.ndarray) -> np.ndarray:
        return (1.0 + np.asarray(z, dtype=float)) ** power

    return factor


def shape_for_kernel_variant(variant: dict, en_rows: list[dict], nz_rows: list[dict]) -> np.ndarray:
    theta_arcmin = np.geomspace(0.5, 300.0, 256)
    _constants, power = janus_holst_weyl_power_factory(eta_holst=0.0, spectral_index=0.5)
    xi_plus, xi_minus = janus_xi_curves_for_kids_bins(
        nz_rows,
        theta_arcmin,
        weyl_power=power,
        distance_kernel=variant["distance_kernel"],
        projection_factor=projection_factor_for_power(float(variant["projection_power"])),
    )
    return np.asarray(cosebis_vector_from_xi(theta_arcmin, xi_plus, xi_minus, en_rows, n_max=5), dtype=float)


def shape_for_distance_kernel(distance_kernel: str, en_rows: list[dict], nz_rows: list[dict]) -> np.ndarray:
    variant = next(item for item in kernel_variant_options() if item["name"] == distance_kernel)
    return shape_for_kernel_variant(variant, en_rows, nz_rows)


def build_payload() -> dict:
    contract = build_cosebis_contract()
    en_rows, nz_rows = extract_rows()
    observed, covariance = slice_contract(contract, scale_cut_indices())
    rows = []
    for variant in kernel_variant_options():
        shape = shape_for_kernel_variant(variant, en_rows, nz_rows)
        amplitude, chi2 = best_amplitude(observed, shape, covariance)
        rows.append(
            {
                "kernel_variant": variant["name"],
                "distance_kernel": variant["distance_kernel"],
                "projection_power": variant["projection_power"],
                "eta_holst": 0.0,
                "spectral_index": 0.5,
                "best_amplitude": amplitude,
                "chi2": chi2,
                "dof": int(observed.size - 1),
                "chi2_per_dof": chi2 / (observed.size - 1),
            }
        )
    best = min(rows, key=lambda row: row["chi2"])
    return {
        "description": "Named Janus distance-kernel audit for KiDS-1000.",
        "status": "diagnostic-distance-kernel-audit-computed",
        "dimension": int(observed.size),
        "rows": rows,
        "best_kernel_variant": best["kernel_variant"],
        "best_chi2_per_dof": best["chi2_per_dof"],
        "prediction_ready": False,
        "boundary": (
            "The named kernels are geometric/projection variants, but this audit still uses "
            "KiDS-inspected eta/tilt and a refitted amplitude."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# KiDS-1000 Janus-Holst Distance-Kernel Audit",
        "",
        payload["description"],
        "",
        f"Status: `{payload['status']}`",
        f"Dimension: `{payload['dimension']}`",
        f"Best kernel variant: `{payload['best_kernel_variant']}`",
        f"Best chi2/dof: `{payload['best_chi2_per_dof']:.6g}`",
        f"Prediction ready: `{payload['prediction_ready']}`",
        "",
        "| kernel variant | distance kernel | projection power | best amplitude | chi2 | dof | chi2/dof |",
        "|---|---|---:|---:|---:|---:|---:|",
    ]
    for row in payload["rows"]:
        lines.append(
            f"| {row['kernel_variant']} | {row['distance_kernel']} | {row['projection_power']:.6g} | "
            f"{row['best_amplitude']:.6g} | "
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
