from __future__ import annotations

from argparse import ArgumentParser
from pathlib import Path
import json
import time

import numpy as np

from janus_lab.field_statistics import pearson_correlation, sigma_r_3d
from janus_lab.initial_conditions import (
    bounded_anticorrelated_contrasts_3d,
    bounded_anticorrelated_contrasts_for_sigma_r_3d,
    gaussian_random_field_3d,
    paired_lognormal_contrasts_for_sigma_r_3d,
)
from janus_lab.lensing import positive_photon_lensing_sigma_r_3d
from janus_lab.physical_units import PhysicalBoxCalibration


REPORT_PATH = Path("outputs/reports/lensing_sigma8_observable.md")
JSON_PATH = Path("outputs/reports/lensing_sigma8_observable.json")


def parse_args():
    parser = ArgumentParser()
    parser.add_argument("--grid", type=int, default=175)
    parser.add_argument("--box-size-mpc", type=float, default=1000.0)
    parser.add_argument("--h0", type=float, default=70.0)
    parser.add_argument("--omega-abs", type=float, default=0.315)
    parser.add_argument("--target-sigma8", type=float, default=0.8)
    parser.add_argument("--seed", type=int, default=20260619)
    parser.add_argument("--spectral-index", type=float, default=1.0)
    parser.add_argument("--cutoff-fraction", type=float, default=0.5)
    parser.add_argument(
        "--bounded-shape-amplitudes",
        default="0.1,0.2,0.5,1,2,4,8,16,32",
    )
    parser.add_argument("--allow-unresolved", action="store_true")
    return parser.parse_args()


def parse_float_list(text: str) -> np.ndarray:
    values = np.asarray([float(item.strip()) for item in text.split(",") if item.strip()], dtype=float)
    if values.size == 0 or np.any(values <= 0.0):
        raise ValueError("bounded shape amplitudes must be positive.")
    return values


def densities_from_contrasts(positive_contrast: np.ndarray, negative_contrast: np.ndarray):
    return 1.0 + positive_contrast, 1.0 + negative_contrast


def row_for_fields(name: str, fields, box_size: float, radius: float) -> dict:
    positive_density, negative_density = densities_from_contrasts(
        fields.positive_contrast,
        fields.negative_contrast,
    )
    return {
        "family": name,
        "positive_sigma8": sigma_r_3d(fields.positive_contrast, box_size, radius),
        "negative_sigma8": sigma_r_3d(fields.negative_contrast, box_size, radius),
        "lensing_sigma8_plus": positive_photon_lensing_sigma_r_3d(
            positive_density,
            negative_density,
            box_size=box_size,
            radius=radius,
        ),
        "sector_correlation": pearson_correlation(
            fields.positive_contrast,
            fields.negative_contrast,
        ),
        "positive_density_safe": bool(np.min(positive_density) > 0.0),
        "negative_density_safe": bool(np.min(negative_density) > 0.0),
    }


def main() -> None:
    args = parse_args()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    grid_shape = (args.grid, args.grid, args.grid)
    calibration = PhysicalBoxCalibration.from_total_absolute_omega(
        box_size_mpc=args.box_size_mpc,
        grid_shape=grid_shape,
        h0_km_s_mpc=args.h0,
        omega_abs=args.omega_abs,
        positive_fraction=0.5,
    )
    if not calibration.resolves_radius(calibration.sigma8_radius_mpc) and not args.allow_unresolved:
        raise ValueError(
            "grid does not resolve sigma8 radius; pass --allow-unresolved only for diagnostics."
        )

    start = time.perf_counter()
    gaussian = gaussian_random_field_3d(
        grid_shape,
        args.box_size_mpc,
        seed=args.seed,
        target_rms=1.0,
        spectral_index=args.spectral_index,
        cutoff_fraction=args.cutoff_fraction,
    )
    lognormal_fields, lognormal_amplitude = paired_lognormal_contrasts_for_sigma_r_3d(
        gaussian,
        box_size=args.box_size_mpc,
        radius=calibration.sigma8_radius_mpc,
        target_sigma=args.target_sigma8,
    )
    bounded_shape_values = parse_float_list(args.bounded_shape_amplitudes)
    bounded_scan = []
    for shape in bounded_shape_values:
        candidate_fields = bounded_anticorrelated_contrasts_3d(
            gaussian,
            shape_amplitude=float(shape),
        )
        bounded_scan.append(
            {
                "shape_amplitude": float(shape),
                "capacity_sigma8": sigma_r_3d(
                    candidate_fields.positive_contrast,
                    args.box_size_mpc,
                    calibration.sigma8_radius_mpc,
                ),
                "fields": candidate_fields,
            }
        )
    best_bounded = max(bounded_scan, key=lambda row: row["capacity_sigma8"])
    try:
        bounded_fields, bounded_capacity = bounded_anticorrelated_contrasts_for_sigma_r_3d(
            gaussian,
            box_size=args.box_size_mpc,
            radius=calibration.sigma8_radius_mpc,
            target_sigma=args.target_sigma8,
            shape_amplitude=best_bounded["shape_amplitude"],
        )
        bounded_row = row_for_fields(
            "bounded_exact_anticorrelation",
            bounded_fields,
            args.box_size_mpc,
            calibration.sigma8_radius_mpc,
        )
        bounded_row["capacity_sigma8"] = bounded_capacity
    except ValueError:
        bounded_fields = best_bounded["fields"]
        bounded_capacity = best_bounded["capacity_sigma8"]
        bounded_row = row_for_fields(
            "bounded_exact_anticorrelation_capacity",
            bounded_fields,
            args.box_size_mpc,
            calibration.sigma8_radius_mpc,
        )
        bounded_row["capacity_sigma8"] = bounded_capacity
        bounded_row["attains_target"] = False

    rows = [
        row_for_fields(
            "lognormal_positive_density",
            lognormal_fields,
            args.box_size_mpc,
            calibration.sigma8_radius_mpc,
        ),
        bounded_row,
    ]
    elapsed = time.perf_counter() - start
    payload = {
        "description": "Sigma8 diagnostic on the Janus positive-sector weak-lensing source.",
        "source_formula": "delta_lens_plus = ((rho_plus - rho_minus_abs) - mean(rho_plus - rho_minus_abs)) / mean(rho_plus + rho_minus_abs)",
        "grid_shape": list(grid_shape),
        "box_size_mpc": args.box_size_mpc,
        "sigma8_radius_mpc": calibration.sigma8_radius_mpc,
        "cell_size_mpc": list(calibration.cell_size_mpc),
        "target_sigma8": args.target_sigma8,
        "lognormal_amplitude": lognormal_amplitude,
        "bounded_best_shape_amplitude": best_bounded["shape_amplitude"],
        "bounded_best_capacity_sigma8": bounded_capacity,
        "rows": rows,
        "generation_seconds": elapsed,
        "boundary": "Diagnostic on the weak-field lensing source only; not a survey shear/S8 likelihood.",
    }
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")

    lines = [
        "# Lensing Sigma8 Observable",
        "",
        "Sigma8 diagnostic on the Janus positive-sector weak-lensing source.",
        "",
        "```text",
        payload["source_formula"],
        "```",
        "",
        "| family | positive sigma8 | negative sigma8 | lensing sigma8 plus | corr | density safe | reading |",
        "|---|---:|---:|---:|---:|---|---|",
    ]
    for row in rows:
        reading = (
            "density-safe scaffold; not a source-derived transfer function"
            if row["family"] == "lognormal_positive_density"
            else "exact anti-correlation diagnostic; target may exceed capacity"
        )
        lines.append(
            f"| {row['family']} | {row['positive_sigma8']:.6g} | "
            f"{row['negative_sigma8']:.6g} | {row['lensing_sigma8_plus']:.6g} | "
            f"{row['sector_correlation']:.6g} | "
            f"{row['positive_density_safe'] and row['negative_density_safe']} | {reading} |"
        )
    lines.extend(
        [
            "",
            f"Grid: `{args.grid}^3`, sigma8 radius: `{calibration.sigma8_radius_mpc:.6g} Mpc`, generation: `{elapsed:.6g} s`.",
            f"JSON: `{JSON_PATH}`",
            "",
            "Boundary: diagnostic on the weak-field lensing source only; not a survey shear/S8 likelihood.",
            "",
        ]
    )
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {JSON_PATH}")


if __name__ == "__main__":
    main()
