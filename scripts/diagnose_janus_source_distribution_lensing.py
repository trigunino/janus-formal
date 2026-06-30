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
from janus_lab.lensing import (
    janus_source_distribution_lensing_weights,
    positive_photon_convergence_proxy_2d,
    shear_from_convergence_proxy_2d,
    shear_proxy_rms,
)
from janus_lab.models import JanusExpansion
from janus_lab.physical_units import PhysicalBoxCalibration


REPORT_PATH = Path("outputs/reports/janus_source_distribution_lensing.md")
JSON_PATH = Path("outputs/reports/janus_source_distribution_lensing.json")


def parse_args():
    parser = ArgumentParser()
    parser.add_argument("--grid", type=int, default=175)
    parser.add_argument("--box-size-mpc", type=float, default=1000.0)
    parser.add_argument("--h0", type=float, default=70.0)
    parser.add_argument("--omega-abs", type=float, default=0.315)
    parser.add_argument("--target-sigma8", type=float, default=0.8)
    parser.add_argument("--source-redshifts", default="0.8,1.2,1.6,2.0,2.4,2.8")
    parser.add_argument("--source-weights", default="")
    parser.add_argument("--q0", type=float, default=-0.087)
    parser.add_argument("--seed", type=int, default=20260619)
    parser.add_argument("--spectral-index", type=float, default=1.0)
    parser.add_argument("--cutoff-fraction", type=float, default=0.5)
    parser.add_argument("--bounded-shape-amplitudes", default="0.1,0.2,0.5,1,2,4,8,16,32")
    parser.add_argument("--axis", type=int, default=2)
    parser.add_argument("--allow-unresolved", action="store_true")
    return parser.parse_args()


def parse_float_list(text: str) -> np.ndarray:
    values = np.asarray([float(item.strip()) for item in text.split(",") if item.strip()], dtype=float)
    if values.size == 0:
        raise ValueError("float list must not be empty.")
    return values


def source_weights_for(args) -> tuple[np.ndarray, np.ndarray]:
    redshifts = parse_float_list(args.source_redshifts)
    if args.source_weights.strip():
        weights = parse_float_list(args.source_weights)
    else:
        weights = np.ones_like(redshifts, dtype=float)
    if redshifts.shape != weights.shape:
        raise ValueError("source redshifts and weights must have the same length.")
    return redshifts, weights


def densities_from_contrasts(fields):
    return 1.0 + fields.positive_contrast, 1.0 + fields.negative_contrast


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


def row_for_observable(name: str, fields, weights: np.ndarray, axis: int, box_size_mpc: float, bin_edges: np.ndarray):
    positive_density, negative_density = densities_from_contrasts(fields)
    kappa = positive_photon_convergence_proxy_2d(
        positive_density,
        negative_density,
        axis=axis,
        weights=weights,
    )
    gamma1, gamma2 = shear_from_convergence_proxy_2d(kappa, box_size=box_size_mpc)
    spectrum1 = radial_power_spectrum_2d(gamma1, box_size=box_size_mpc, bin_edges=bin_edges)
    spectrum2 = radial_power_spectrum_2d(gamma2, box_size=box_size_mpc, bin_edges=bin_edges)
    first = next((i for i, count in enumerate(spectrum1.mode_counts) if count > 0), 0)
    return {
        "family": name,
        "kappa_distribution_rms": rms(kappa),
        "shear_distribution_rms": shear_proxy_rms(gamma1, gamma2),
        "first_k_center_inv_mpc": float(spectrum1.k_centers[first]),
        "first_shear_power": float(spectrum1.power[first] + spectrum2.power[first]),
        "first_mode_count": int(spectrum1.mode_counts[first]),
    }


def main() -> None:
    args = parse_args()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    source_redshifts, source_weights = source_weights_for(args)
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
    model = JanusExpansion.from_q0(args.q0)
    z_slices = np.linspace(0.0, float(np.max(source_redshifts)), grid_shape[args.axis])
    weights = janus_source_distribution_lensing_weights(
        z_slices,
        source_redshifts,
        source_weights,
        model,
    )
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
        row_for_observable(
            "lognormal_positive_density",
            lognormal_fields,
            weights,
            args.axis,
            args.box_size_mpc,
            bin_edges,
        ),
        row_for_observable(
            "bounded_exact_anticorrelation_capacity",
            bounded_fields,
            weights,
            args.axis,
            args.box_size_mpc,
            bin_edges,
        ),
    ]
    elapsed = time.perf_counter() - start
    payload = {
        "description": "Janus open-distance lensing with an explicit source-redshift distribution.",
        "source_redshifts": source_redshifts.tolist(),
        "source_weights_normalized": (source_weights / float(np.sum(source_weights))).tolist(),
        "grid_shape": list(grid_shape),
        "axis": args.axis,
        "q0": args.q0,
        "weight_sum": float(np.sum(weights)),
        "weight_max": float(np.max(weights)),
        "weight_argmax_index": int(np.argmax(weights)),
        "weight_argmax_redshift": float(z_slices[int(np.argmax(weights))]),
        "lognormal_amplitude": lognormal_amplitude,
        "bounded_best_shape_amplitude": bounded_shape,
        "bounded_best_capacity_sigma8": bounded_capacity,
        "rows": rows,
        "generation_seconds": elapsed,
        "boundary": "Explicit source distribution diagnostic only; default distribution is not survey-derived and is not fitted.",
    }
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")

    lines = [
        "# Janus Source-Distribution Lensing",
        "",
        "Projection using the Janus open-distance kernel integrated over an explicit source-redshift distribution.",
        "",
        f"Sources: `{payload['source_redshifts']}`.",
        f"Peak lens weight redshift: `{payload['weight_argmax_redshift']:.6g}`.",
        "",
        "| family | kappa RMS | shear RMS | first k [1/Mpc] | first shear power |",
        "|---|---:|---:|---:|---:|",
    ]
    for row in rows:
        lines.append(
            f"| {row['family']} | {row['kappa_distribution_rms']:.6g} | "
            f"{row['shear_distribution_rms']:.6g} | {row['first_k_center_inv_mpc']:.6g} | "
            f"{row['first_shear_power']:.6g} |"
        )
    lines.extend(
        [
            "",
            f"Grid: `{args.grid}^3`, generation: `{elapsed:.6g} s`.",
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
