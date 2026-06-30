from __future__ import annotations

from argparse import ArgumentParser
from pathlib import Path
import json
import time

import numpy as np

from janus_lab.field_statistics import (
    normalize_field_to_sigma_r_3d,
    rms,
    sigma_r_3d,
)
from janus_lab.initial_conditions import displacement_from_contrast_3d, gaussian_random_field_3d
from janus_lab.particle_mesh_3d_vectorized import (
    create_two_sector_lattice_state_from_displacements_3d,
)
from janus_lab.physical_units import PhysicalBoxCalibration


REPORT_PATH = Path("outputs/reports/sigma8_normalized_ic_3d.md")
JSON_PATH = Path("outputs/reports/sigma8_normalized_ic_3d.json")


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
    parser.add_argument("--build-state", action="store_true")
    parser.add_argument("--displacement-scale", type=float, default=0.1)
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
    raw_field = gaussian_random_field_3d(
        grid_shape,
        args.box_size_mpc,
        seed=args.seed,
        target_rms=1.0,
        spectral_index=args.spectral_index,
        cutoff_fraction=args.cutoff_fraction,
    )
    raw_sigma8 = sigma_r_3d(
        raw_field,
        box_size=args.box_size_mpc,
        radius=calibration.sigma8_radius_mpc,
    )
    raw_min = float(np.min(raw_field))
    max_density_safe_sigma8 = raw_sigma8 / abs(raw_min) if raw_min < 0.0 else float("inf")
    positive = normalize_field_to_sigma_r_3d(
        raw_field,
        box_size=args.box_size_mpc,
        radius=calibration.sigma8_radius_mpc,
        target_sigma=args.target_sigma8,
    )
    negative = -positive
    achieved_sigma8 = sigma_r_3d(
        positive,
        box_size=args.box_size_mpc,
        radius=calibration.sigma8_radius_mpc,
    )
    fraction_below_minus_one = float(np.mean(positive < -1.0))
    generation_seconds = time.perf_counter() - start

    state_metrics = None
    if args.build_state:
        state_start = time.perf_counter()
        positive_displacement = displacement_from_contrast_3d(
            positive,
            box_size=args.box_size_mpc,
            displacement_scale=args.displacement_scale,
        )
        state = create_two_sector_lattice_state_from_displacements_3d(
            positive_displacement,
            -positive_displacement,
            box_size=args.box_size_mpc,
            mass_abs=calibration.positive_particle_mass_msun,
        )
        state_metrics = {
            "build_state_seconds": time.perf_counter() - state_start,
            "particle_count": int(len(state.positions)),
            "positions_finite": bool(np.isfinite(state.positions).all()),
            "max_displacement_mpc": float(
                np.linalg.norm(positive_displacement.reshape(-1, 3), axis=1).max()
            ),
        }

    payload = {
        "grid_shape": list(grid_shape),
        "box_size_mpc": args.box_size_mpc,
        "h0_km_s_mpc": args.h0,
        "sigma8_radius_mpc": calibration.sigma8_radius_mpc,
        "cell_size_mpc": list(calibration.cell_size_mpc),
        "resolves_sigma8": calibration.resolves_radius(calibration.sigma8_radius_mpc),
        "target_sigma8": args.target_sigma8,
        "raw_sigma8": raw_sigma8,
        "max_density_safe_sigma8_for_this_seed": max_density_safe_sigma8,
        "achieved_sigma8": achieved_sigma8,
        "normalization_factor": args.target_sigma8 / raw_sigma8,
        "positive_rms": rms(positive),
        "positive_min": float(np.min(positive)),
        "positive_max": float(np.max(positive)),
        "fraction_below_minus_one": fraction_below_minus_one,
        "density_contrast_safe": fraction_below_minus_one == 0.0,
        "negative_rms": rms(negative),
        "generation_seconds": generation_seconds,
        "state_metrics": state_metrics,
        "boundary": "Amplitude-normalized Gaussian IC only; not a Janus-derived transfer function.",
    }
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")

    lines = [
        "# Sigma8-Normalized 3D IC",
        "",
        "Gaussian two-sector contrast field normalized on the resolved `8 h^-1 Mpc` scale.",
        "",
        "| metric | value |",
        "|---|---:|",
        f"| grid | {args.grid}^3 |",
        f"| box size | {args.box_size_mpc:.6g} Mpc |",
        f"| cell size | {calibration.cell_size_mpc[0]:.6g} Mpc |",
        f"| sigma8 radius | {calibration.sigma8_radius_mpc:.6g} Mpc |",
        f"| resolves sigma8 | {calibration.resolves_radius(calibration.sigma8_radius_mpc)} |",
        f"| target sigma8 | {args.target_sigma8:.6g} |",
        f"| raw sigma8 | {raw_sigma8:.6g} |",
        f"| max density-safe sigma8 for this seed | {max_density_safe_sigma8:.6g} |",
        f"| achieved sigma8 | {achieved_sigma8:.6g} |",
        f"| normalization factor | {args.target_sigma8 / raw_sigma8:.6g} |",
        f"| positive RMS | {rms(positive):.6g} |",
        f"| positive min | {float(np.min(positive)):.6g} |",
        f"| positive max | {float(np.max(positive)):.6g} |",
        f"| fraction delta < -1 | {fraction_below_minus_one:.6g} |",
        f"| density contrast safe | {fraction_below_minus_one == 0.0} |",
        f"| generation time | {generation_seconds:.6g} s |",
    ]
    if state_metrics is not None:
        lines.extend(
            [
                f"| vector state particles | {state_metrics['particle_count']} |",
                f"| vector state build time | {state_metrics['build_state_seconds']:.6g} s |",
                f"| max displacement | {state_metrics['max_displacement_mpc']:.6g} Mpc |",
                f"| positions finite | {state_metrics['positions_finite']} |",
            ]
        )
    lines.extend(
        [
            "",
            f"JSON: `{JSON_PATH}`",
            "",
            "Boundary: this is a controlled Gaussian amplitude normalization. A field with `delta < -1` is not directly usable as a positive-density IC. This is not yet a Janus-derived transfer function, not a CMB fit, and not an observational proof.",
            "",
        ]
    )
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {JSON_PATH}")


if __name__ == "__main__":
    main()
