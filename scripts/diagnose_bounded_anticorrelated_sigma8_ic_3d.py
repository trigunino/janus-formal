from __future__ import annotations

from argparse import ArgumentParser
from pathlib import Path
import csv
import json
import time

import numpy as np

from janus_lab.field_statistics import pearson_correlation, rms, sigma_r_3d
from janus_lab.initial_conditions import (
    bounded_anticorrelated_contrasts_3d,
    bounded_anticorrelated_contrasts_for_sigma_r_3d,
    gaussian_random_field_3d,
)
from janus_lab.physical_units import PhysicalBoxCalibration


REPORT_PATH = Path("outputs/reports/bounded_anticorrelated_sigma8_ic_3d.md")
CSV_PATH = Path("outputs/reports/bounded_anticorrelated_sigma8_ic_3d_scan.csv")
JSON_PATH = Path("outputs/reports/bounded_anticorrelated_sigma8_ic_3d.json")


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
    parser.add_argument("--allow-unresolved", action="store_true")
    return parser.parse_args()


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
    shape_values = np.asarray([0.1, 0.2, 0.5, 1.0, 2.0, 4.0, 8.0, 16.0, 32.0])
    scan_rows = []
    for shape in shape_values:
        fields = bounded_anticorrelated_contrasts_3d(gaussian, shape_amplitude=float(shape))
        scan_rows.append(
            {
                "shape_amplitude": float(shape),
                "max_sigma8": sigma_r_3d(
                    fields.positive_contrast,
                    box_size=args.box_size_mpc,
                    radius=calibration.sigma8_radius_mpc,
                ),
                "positive_rms": rms(fields.positive_contrast),
                "positive_min": float(np.min(fields.positive_contrast)),
                "positive_max": float(np.max(fields.positive_contrast)),
                "sector_correlation": pearson_correlation(
                    fields.positive_contrast,
                    fields.negative_contrast,
                ),
            }
        )
    best = max(scan_rows, key=lambda row: row["max_sigma8"])
    attainable = best["max_sigma8"] >= args.target_sigma8
    selected_metrics = None
    if attainable:
        selected_fields, selected_capacity = bounded_anticorrelated_contrasts_for_sigma_r_3d(
            gaussian,
            box_size=args.box_size_mpc,
            radius=calibration.sigma8_radius_mpc,
            target_sigma=args.target_sigma8,
            shape_amplitude=best["shape_amplitude"],
        )
        selected_metrics = {
            "capacity_sigma8": selected_capacity,
            "positive_sigma8": sigma_r_3d(
                selected_fields.positive_contrast,
                box_size=args.box_size_mpc,
                radius=calibration.sigma8_radius_mpc,
            ),
            "negative_sigma8": sigma_r_3d(
                selected_fields.negative_contrast,
                box_size=args.box_size_mpc,
                radius=calibration.sigma8_radius_mpc,
            ),
            "positive_rms": rms(selected_fields.positive_contrast),
            "positive_min": float(np.min(selected_fields.positive_contrast)),
            "positive_max": float(np.max(selected_fields.positive_contrast)),
            "sector_correlation": pearson_correlation(
                selected_fields.positive_contrast,
                selected_fields.negative_contrast,
            ),
        }
    elapsed = time.perf_counter() - start

    with CSV_PATH.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(scan_rows[0].keys()))
        writer.writeheader()
        writer.writerows(scan_rows)

    payload = {
        "grid_shape": list(grid_shape),
        "box_size_mpc": args.box_size_mpc,
        "sigma8_radius_mpc": calibration.sigma8_radius_mpc,
        "target_sigma8": args.target_sigma8,
        "best_capacity": best,
        "target_attainable": attainable,
        "selected_metrics": selected_metrics,
        "elapsed_seconds": elapsed,
        "boundary": "Bounded anti-correlated toy IC. Not a Janus-derived transfer function.",
    }
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")

    lines = [
        "# Bounded Anti-Correlated Sigma8 IC 3D",
        "",
        "Density-safe exact anti-correlation test using `delta = A tanh(...)`.",
        "",
        "| metric | value |",
        "|---|---:|",
        f"| grid | {args.grid}^3 |",
        f"| box size | {args.box_size_mpc:.6g} Mpc |",
        f"| cell size | {calibration.cell_size_mpc[0]:.6g} Mpc |",
        f"| sigma8 radius | {calibration.sigma8_radius_mpc:.6g} Mpc |",
        f"| target sigma8 | {args.target_sigma8:.6g} |",
        f"| best shape amplitude | {best['shape_amplitude']:.6g} |",
        f"| best bounded sigma8 capacity | {best['max_sigma8']:.6g} |",
        f"| target attainable | {attainable} |",
        f"| elapsed | {elapsed:.6g} s |",
        "",
        "| shape amplitude | max sigma8 | RMS | min | max | corr |",
        "|---:|---:|---:|---:|---:|---:|",
    ]
    for row in scan_rows:
        lines.append(
            f"| {row['shape_amplitude']:.6g} | {row['max_sigma8']:.6g} | "
            f"{row['positive_rms']:.6g} | {row['positive_min']:.6g} | "
            f"{row['positive_max']:.6g} | {row['sector_correlation']:.6g} |"
        )
    if selected_metrics is not None:
        lines.extend(
            [
                "",
                "| selected metric | value |",
                "|---|---:|",
                f"| positive sigma8 | {selected_metrics['positive_sigma8']:.6g} |",
                f"| negative sigma8 | {selected_metrics['negative_sigma8']:.6g} |",
                f"| sector correlation | {selected_metrics['sector_correlation']:.6g} |",
                f"| positive min | {selected_metrics['positive_min']:.6g} |",
                f"| positive max | {selected_metrics['positive_max']:.6g} |",
            ]
        )
    lines.extend(
        [
            "",
            f"CSV: `{CSV_PATH}`",
            f"JSON: `{JSON_PATH}`",
            "",
            "Boundary: this preserves exact anti-correlation and density positivity, but it is still a toy transform, not a Janus-derived transfer function.",
            "",
        ]
    )
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {CSV_PATH}")
    print(f"Wrote {JSON_PATH}")


if __name__ == "__main__":
    main()
