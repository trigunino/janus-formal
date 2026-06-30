from __future__ import annotations

from argparse import ArgumentParser
from pathlib import Path
import json
import time

import numpy as np

from janus_lab.field_statistics import radial_power_spectrum_2d, rms, sigma_r_3d
from janus_lab.initial_conditions import (
    bounded_anticorrelated_contrasts_3d,
    gaussian_random_field_3d,
    paired_lognormal_contrasts_for_sigma_r_3d,
)
from janus_lab.lensing import positive_photon_convergence_proxy_2d
from janus_lab.physical_units import PhysicalBoxCalibration


REPORT_PATH = Path("outputs/reports/weak_lensing_projection.md")
JSON_PATH = Path("outputs/reports/weak_lensing_projection.json")


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
    parser.add_argument("--bounded-shape-amplitudes", default="0.1,0.2,0.5,1,2,4,8,16,32")
    parser.add_argument("--axis", type=int, default=2)
    parser.add_argument("--allow-unresolved", action="store_true")
    return parser.parse_args()


def parse_float_list(text: str) -> np.ndarray:
    values = np.asarray([float(item.strip()) for item in text.split(",") if item.strip()], dtype=float)
    if values.size == 0 or np.any(values <= 0.0):
        raise ValueError("bounded shape amplitudes must be positive.")
    return values


def densities_from_contrasts(fields):
    return 1.0 + fields.positive_contrast, 1.0 + fields.negative_contrast


def projection_row(name: str, fields, box_size_mpc: float, axis: int, bin_edges: np.ndarray) -> dict:
    positive_density, negative_density = densities_from_contrasts(fields)
    kappa = positive_photon_convergence_proxy_2d(
        positive_density,
        negative_density,
        axis=axis,
    )
    spectrum = radial_power_spectrum_2d(kappa, box_size=box_size_mpc, bin_edges=bin_edges)
    first_nonempty = next(
        (
            index
            for index, count in enumerate(spectrum.mode_counts)
            if count > 0 and spectrum.k_centers[index] > 0.0
        ),
        0,
    )
    return {
        "family": name,
        "kappa_proxy_rms": rms(kappa),
        "kappa_proxy_min": float(np.min(kappa)),
        "kappa_proxy_max": float(np.max(kappa)),
        "first_k_center_inv_mpc": float(spectrum.k_centers[first_nonempty]),
        "first_projected_power": float(spectrum.power[first_nonempty]),
        "first_mode_count": int(spectrum.mode_counts[first_nonempty]),
    }


def best_bounded_fields(gaussian: np.ndarray, box_size_mpc: float, radius_mpc: float, shapes: np.ndarray):
    best_fields = None
    best_sigma = -1.0
    best_shape = None
    for shape in shapes:
        fields = bounded_anticorrelated_contrasts_3d(gaussian, shape_amplitude=float(shape))
        capacity = sigma_r_3d(fields.positive_contrast, box_size_mpc, radius_mpc)
        if capacity > best_sigma:
            best_fields = fields
            best_sigma = capacity
            best_shape = float(shape)
    return best_fields, best_shape, best_sigma


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
    bounded_fields, bounded_shape, bounded_capacity = best_bounded_fields(
        gaussian,
        args.box_size_mpc,
        calibration.sigma8_radius_mpc,
        parse_float_list(args.bounded_shape_amplitudes),
    )
    fundamental = 2.0 * np.pi / args.box_size_mpc
    bin_edges = fundamental * np.asarray([0.5, 1.5, 2.5, 4.5, 8.5, 16.5, 32.5])
    rows = [
        projection_row("lognormal_positive_density", lognormal_fields, args.box_size_mpc, args.axis, bin_edges),
        projection_row("bounded_exact_anticorrelation_capacity", bounded_fields, args.box_size_mpc, args.axis, bin_edges),
    ]
    elapsed = time.perf_counter() - start
    payload = {
        "description": "Uniform line-of-sight projection of the Janus positive-sector weak-lensing source.",
        "projection_formula": "kappa_plus_proxy(x_perp) = mean_axis(delta_lens_plus)",
        "grid_shape": list(grid_shape),
        "box_size_mpc": args.box_size_mpc,
        "axis": args.axis,
        "sigma8_radius_mpc": calibration.sigma8_radius_mpc,
        "target_sigma8": args.target_sigma8,
        "lognormal_amplitude": lognormal_amplitude,
        "bounded_best_shape_amplitude": bounded_shape,
        "bounded_best_capacity_sigma8": bounded_capacity,
        "rows": rows,
        "generation_seconds": elapsed,
        "boundary": "Uniform projection proxy only; no Janus tomographic kernel, no shear estimator, no survey likelihood.",
    }
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")

    lines = [
        "# Weak Lensing Projection",
        "",
        "Uniform line-of-sight projection of the Janus positive-sector weak-lensing source.",
        "",
        "```text",
        payload["projection_formula"],
        "```",
        "",
        "| family | kappa proxy RMS | min | max | first k [1/Mpc] | first projected power | modes |",
        "|---|---:|---:|---:|---:|---:|---:|",
    ]
    for row in rows:
        lines.append(
            f"| {row['family']} | {row['kappa_proxy_rms']:.6g} | "
            f"{row['kappa_proxy_min']:.6g} | {row['kappa_proxy_max']:.6g} | "
            f"{row['first_k_center_inv_mpc']:.6g} | {row['first_projected_power']:.6g} | "
            f"{row['first_mode_count']} |"
        )
    lines.extend(
        [
            "",
            f"Grid: `{args.grid}^3`, projection axis: `{args.axis}`, generation: `{elapsed:.6g} s`.",
            f"JSON: `{JSON_PATH}`",
            "",
            payload["boundary"],
            "",
        ]
    )
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {JSON_PATH}")


if __name__ == "__main__":
    main()
