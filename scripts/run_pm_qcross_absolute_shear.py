from __future__ import annotations

from argparse import ArgumentParser
from pathlib import Path
import json
import time

import numpy as np

from janus_lab.cosmological_pm import scale_factor_sequence
from janus_lab.field_statistics import radial_power_spectrum_2d, rms
from janus_lab.initial_conditions import (
    bounded_anticorrelated_contrasts_3d,
    displacement_from_contrast_3d,
    gaussian_random_field_3d,
)
from janus_lab.lensing import (
    janus_absolute_lensing_coefficients,
    project_lensing_contrast_2d_with_coefficients,
    shear_from_convergence_proxy_2d,
    shear_proxy_rms,
)
from janus_lab.models import JanusExpansion
from janus_lab.particle_mesh_3d_vectorized import (
    cosmological_pm_step_3d_vectorized,
    create_two_sector_lattice_state_from_displacements_3d,
    deposit_cloud_in_cell_3d_vectorized,
    deposit_sector_cloud_in_cell_3d_vectorized,
    estimate_vectorized_pm_memory_bytes,
)
from janus_lab.physical_units import hubble_time_gyr

try:
    from scripts.diagnose_pm_state_qcross import (
        DEFAULT_PHOTON_DIRECTION,
        _stats,
        negative_qcross_from_state,
    )
except ModuleNotFoundError:
    from diagnose_pm_state_qcross import (
        DEFAULT_PHOTON_DIRECTION,
        _stats,
        negative_qcross_from_state,
    )


REPORT_PATH = Path("outputs/reports/pm_qcross_absolute_shear.md")
JSON_PATH = Path("outputs/reports/pm_qcross_absolute_shear.json")


def parse_float_list(text: str) -> np.ndarray:
    values = np.asarray([float(item.strip()) for item in text.split(",") if item.strip()])
    if values.size == 0:
        raise ValueError("list must not be empty.")
    return values


def gb(value: int) -> float:
    return value / 1024.0**3


def qcross_lensing_contrast(
    state,
    *,
    grid_shape: tuple[int, int, int],
    box_size: float,
    box_size_mpc: float,
    time_unit_gyr: float,
) -> tuple[np.ndarray, dict[str, float]]:
    negative, _, velocities_km_s, q_cross = negative_qcross_from_state(
        state,
        box_size_mpc=box_size_mpc,
        time_unit_gyr=time_unit_gyr,
        photon_direction=DEFAULT_PHOTON_DIRECTION,
    )
    positive_density, negative_density = deposit_cloud_in_cell_3d_vectorized(
        state,
        grid_shape=grid_shape,
        box_size=box_size,
    )
    qcross_weights = np.ones(len(state.positions), dtype=float)
    qcross_weights[negative] = q_cross
    negative_qcross_density = deposit_sector_cloud_in_cell_3d_vectorized(
        state,
        -1,
        grid_shape=grid_shape,
        box_size=box_size,
        particle_weight_factor=qcross_weights,
    )
    source = positive_density - negative_qcross_density
    scale = float(np.mean(positive_density + negative_density))
    contrast = (source - float(np.mean(source))) / scale
    speed = np.linalg.norm(velocities_km_s, axis=1)
    return contrast, {
        "qcross_min": _stats(q_cross)["min"],
        "qcross_mean": _stats(q_cross)["mean"],
        "qcross_max": _stats(q_cross)["max"],
        "speed_max_km_s": _stats(speed)["max"],
        "lensing_contrast_rms": rms(contrast),
    }


def parse_args():
    parser = ArgumentParser()
    parser.add_argument("--grid", type=int, default=64)
    parser.add_argument("--steps", type=int, default=4)
    parser.add_argument("--dt", type=float, default=0.0001)
    parser.add_argument("--gravity-scale", type=float, default=0.5)
    parser.add_argument("--box-size-mpc", type=float, default=1000.0)
    parser.add_argument("--h0", type=float, default=70.0)
    parser.add_argument("--omega-abs", type=float, default=0.315)
    parser.add_argument("--q0", type=float, default=-0.087)
    parser.add_argument("--source-redshifts", default="0.8,1.2,1.6,2.0")
    parser.add_argument("--source-weights", default="")
    parser.add_argument("--axis", type=int, default=2)
    parser.add_argument("--seed", type=int, default=20260621)
    parser.add_argument("--shape-amplitude", type=float, default=1.0)
    parser.add_argument("--displacement-scale", type=float, default=0.05)
    parser.add_argument(
        "--ic-family",
        choices=("bounded-gaussian", "analytic-multimode"),
        default="bounded-gaussian",
    )
    parser.add_argument(
        "--mass-normalization",
        choices=("fixed-total", "fixed-particle"),
        default="fixed-total",
    )
    return parser.parse_args()


def analytic_multimode_field_3d(grid_shape: tuple[int, int, int]) -> np.ndarray:
    nx, ny, nz = grid_shape
    x = (np.arange(nx, dtype=float) + 0.5) / nx
    y = (np.arange(ny, dtype=float) + 0.5) / ny
    z = (np.arange(nz, dtype=float) + 0.5) / nz
    xx, yy, zz = np.meshgrid(x, y, z, indexing="ij")
    field = (
        np.sin(2.0 * np.pi * xx)
        + 0.7 * np.sin(2.0 * np.pi * yy + 0.3)
        + 0.5 * np.sin(2.0 * np.pi * zz + 0.7)
        + 0.3 * np.sin(2.0 * np.pi * (xx + yy))
        + 0.2 * np.cos(2.0 * np.pi * (xx - zz))
    )
    field -= float(np.mean(field))
    field_rms = rms(field)
    return field if field_rms == 0.0 else field / field_rms


def build_source_derived_state(args, grid_shape: tuple[int, int, int]):
    ic_family = getattr(args, "ic_family", "bounded-gaussian")
    if ic_family == "analytic-multimode":
        gaussian = analytic_multimode_field_3d(grid_shape)
    else:
        gaussian = gaussian_random_field_3d(
            grid_shape,
            box_size=1.0,
            seed=args.seed,
            target_rms=1.0,
            spectral_index=1.0,
            cutoff_fraction=0.5,
        )
    fields = bounded_anticorrelated_contrasts_3d(
        gaussian,
        shape_amplitude=args.shape_amplitude,
    )
    positive_displacement = displacement_from_contrast_3d(
        fields.positive_contrast,
        box_size=1.0,
        displacement_scale=args.displacement_scale,
    )
    negative_displacement = displacement_from_contrast_3d(
        fields.negative_contrast,
        box_size=1.0,
        displacement_scale=args.displacement_scale,
    )
    mass_normalization = getattr(args, "mass_normalization", "fixed-total")
    if mass_normalization == "fixed-total":
        mass_abs = 1.0 / float(np.prod(grid_shape))
    elif mass_normalization == "fixed-particle":
        mass_abs = 1.0
    else:
        raise ValueError("mass_normalization must be 'fixed-total' or 'fixed-particle'.")
    return create_two_sector_lattice_state_from_displacements_3d(
        positive_displacement,
        negative_displacement,
        box_size=1.0,
        mass_abs=mass_abs,
    )


def build_payload(args) -> dict:
    if args.grid <= 0:
        raise ValueError("--grid must be positive.")
    if args.steps <= 1:
        raise ValueError("--steps must be greater than one.")
    grid_shape = (args.grid, args.grid, args.grid)
    if args.axis < 0:
        args.axis += 3
    if args.axis < 0 or args.axis >= 3:
        raise ValueError("--axis is out of range.")
    source_redshifts = parse_float_list(args.source_redshifts)
    source_weights = (
        parse_float_list(args.source_weights)
        if args.source_weights.strip()
        else np.ones_like(source_redshifts)
    )
    if source_redshifts.shape != source_weights.shape:
        raise ValueError("source redshifts and weights must have the same length.")
    weights = source_weights / float(np.sum(source_weights))

    start = time.perf_counter()
    state = build_source_derived_state(args, grid_shape)
    scale_factors = scale_factor_sequence(0.5, 1.0, args.steps)
    expansion_rates = np.asarray(
        JanusExpansion.from_q0(args.q0).e(1.0 / scale_factors - 1.0),
        dtype=float,
    )
    for scale_factor, expansion_rate in zip(scale_factors[:-1], expansion_rates[:-1]):
        state = cosmological_pm_step_3d_vectorized(
            state,
            dt=args.dt,
            scale_factor=float(scale_factor),
            expansion_rate=float(expansion_rate),
            grid_shape=grid_shape,
            box_size=1.0,
            gravity_scale=args.gravity_scale,
            in_place=True,
        )

    time_unit_gyr = hubble_time_gyr(args.h0)
    lensing_contrast, source_metrics = qcross_lensing_contrast(
        state,
        grid_shape=grid_shape,
        box_size=1.0,
        box_size_mpc=args.box_size_mpc,
        time_unit_gyr=time_unit_gyr,
    )
    model = JanusExpansion.from_q0(args.q0)
    z_slices = np.linspace(0.0, float(np.max(source_redshifts)), grid_shape[args.axis])
    coefficients = janus_absolute_lensing_coefficients(
        z_slices,
        source_redshifts,
        weights,
        model,
        h0_km_s_mpc=args.h0,
        omega_abs=args.omega_abs,
    )
    kappa = project_lensing_contrast_2d_with_coefficients(
        lensing_contrast,
        coefficients,
        axis=args.axis,
    )
    gamma1, gamma2 = shear_from_convergence_proxy_2d(kappa, box_size=args.box_size_mpc)
    fundamental = 2.0 * np.pi / args.box_size_mpc
    bin_edges = fundamental * np.asarray([0.5, 1.5, 2.5, 4.5, 8.5, 16.5, 32.5])
    spectrum1 = radial_power_spectrum_2d(gamma1, box_size=args.box_size_mpc, bin_edges=bin_edges)
    spectrum2 = radial_power_spectrum_2d(gamma2, box_size=args.box_size_mpc, bin_edges=bin_edges)
    shear_power = spectrum1.power + spectrum2.power
    first = next((i for i, count in enumerate(spectrum1.mode_counts) if count > 0), 0)
    elapsed = time.perf_counter() - start

    return {
        "description": "Absolute shear diagnostic from PM Q_cross source and Janus lensing coefficients.",
        "initial_state": f"{getattr(args, 'ic_family', 'bounded-gaussian')}_displacement_ic",
        "seed": args.seed,
        "shape_amplitude": args.shape_amplitude,
        "displacement_scale": args.displacement_scale,
        "mass_normalization": getattr(args, "mass_normalization", "fixed-total"),
        "grid": args.grid,
        "steps": args.steps,
        "particle_count": int(len(state.positions)),
        "estimated_core_memory_gb": gb(estimate_vectorized_pm_memory_bytes(grid_shape, len(state.positions))),
        "h0_km_s_mpc": args.h0,
        "time_unit_basis": "H0^-1",
        "time_unit_gyr": time_unit_gyr,
        "omega_abs": args.omega_abs,
        "source_redshifts": source_redshifts.tolist(),
        "source_weights_normalized": weights.tolist(),
        "coefficient_sum": float(np.sum(coefficients)),
        "coefficient_max": float(np.max(coefficients)),
        "coefficient_peak_z": float(z_slices[int(np.argmax(coefficients))]),
        "kappa_abs_rms": rms(kappa),
        "kappa_abs_min": float(np.min(kappa)),
        "kappa_abs_max": float(np.max(kappa)),
        "shear_abs_rms": shear_proxy_rms(gamma1, gamma2),
        "shear_power_bands": [
            {
                "k_center_inv_mpc": float(k_center),
                "power": float(power),
                "mode_count": int(count),
            }
            for k_center, power, count in zip(
                spectrum1.k_centers,
                shear_power,
                spectrum1.mode_counts,
            )
        ],
        "first_k_center_inv_mpc": float(spectrum1.k_centers[first]),
        "first_shear_power": float(shear_power[first]),
        "first_mode_count": int(spectrum1.mode_counts[first]),
        "source_metrics": source_metrics,
        "generation_seconds": elapsed,
        "finite": bool(np.isfinite(kappa).all() and np.isfinite(gamma1).all() and np.isfinite(gamma2).all()),
        "boundary": (
            "Absolute observable diagnostic only. It uses source-derived bounded IC, H0^-1 PM time "
            "calibration, velocity-derived Q_cross source, and current Janus coefficient scaffold; "
            "it is not a survey likelihood."
        ),
    }


def main() -> None:
    args = parse_args()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    payload = build_payload(args)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# PM Q_cross Absolute Shear",
        "",
        payload["description"],
        "",
        "| metric | value |",
        "|---|---:|",
        f"| grid | {payload['grid']}^3 |",
        f"| initial state | {payload['initial_state']} |",
        f"| particles | {payload['particle_count']} |",
        f"| H0 | {payload['h0_km_s_mpc']:.6g} km/s/Mpc |",
        f"| time unit | {payload['time_unit_gyr']:.6g} Gyr |",
        f"| coefficient max | {payload['coefficient_max']:.9g} |",
        f"| coefficient peak z | {payload['coefficient_peak_z']:.9g} |",
        f"| kappa abs RMS | {payload['kappa_abs_rms']:.9g} |",
        f"| shear abs RMS | {payload['shear_abs_rms']:.9g} |",
        f"| first shear power | {payload['first_shear_power']:.9g} |",
        f"| finite | {payload['finite']} |",
        f"| generation seconds | {payload['generation_seconds']:.6g} |",
        "",
        payload["boundary"],
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {JSON_PATH}")


if __name__ == "__main__":
    main()
