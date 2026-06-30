from __future__ import annotations

from argparse import ArgumentParser
from pathlib import Path
import json
import time

import numpy as np

from janus_lab.field_statistics import pearson_correlation, rms, sigma_r_3d
from janus_lab.initial_conditions import (
    gaussian_random_field_3d,
    paired_lognormal_contrasts_for_sigma_r_3d,
)
from janus_lab.physical_units import PhysicalBoxCalibration


REPORT_PATH = Path("outputs/reports/lognormal_sigma8_ic_3d.md")
JSON_PATH = Path("outputs/reports/lognormal_sigma8_ic_3d.json")


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
    fields, amplitude = paired_lognormal_contrasts_for_sigma_r_3d(
        gaussian,
        box_size=args.box_size_mpc,
        radius=calibration.sigma8_radius_mpc,
        target_sigma=args.target_sigma8,
    )
    positive_sigma8 = sigma_r_3d(
        fields.positive_contrast,
        box_size=args.box_size_mpc,
        radius=calibration.sigma8_radius_mpc,
    )
    negative_sigma8 = sigma_r_3d(
        fields.negative_contrast,
        box_size=args.box_size_mpc,
        radius=calibration.sigma8_radius_mpc,
    )
    elapsed = time.perf_counter() - start

    payload = {
        "grid_shape": list(grid_shape),
        "box_size_mpc": args.box_size_mpc,
        "h0_km_s_mpc": args.h0,
        "sigma8_radius_mpc": calibration.sigma8_radius_mpc,
        "cell_size_mpc": list(calibration.cell_size_mpc),
        "resolves_sigma8": calibration.resolves_radius(calibration.sigma8_radius_mpc),
        "target_sigma8": args.target_sigma8,
        "lognormal_amplitude": amplitude,
        "positive_sigma8": positive_sigma8,
        "negative_sigma8": negative_sigma8,
        "positive_rms": rms(fields.positive_contrast),
        "negative_rms": rms(fields.negative_contrast),
        "positive_min": float(np.min(fields.positive_contrast)),
        "negative_min": float(np.min(fields.negative_contrast)),
        "positive_max": float(np.max(fields.positive_contrast)),
        "negative_max": float(np.max(fields.negative_contrast)),
        "sector_correlation": pearson_correlation(
            fields.positive_contrast,
            fields.negative_contrast,
        ),
        "positive_density_safe": bool(np.min(fields.positive_contrast) > -1.0),
        "negative_density_safe": bool(np.min(fields.negative_contrast) > -1.0),
        "generation_seconds": elapsed,
        "boundary": "Lognormal positive-density IC only; not a Janus-derived transfer function.",
    }
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")

    lines = [
        "# Lognormal Sigma8 3D IC",
        "",
        "Positive-density two-sector lognormal IC normalized on the resolved `8 h^-1 Mpc` scale.",
        "",
        "| metric | value |",
        "|---|---:|",
        f"| grid | {args.grid}^3 |",
        f"| box size | {args.box_size_mpc:.6g} Mpc |",
        f"| cell size | {calibration.cell_size_mpc[0]:.6g} Mpc |",
        f"| sigma8 radius | {calibration.sigma8_radius_mpc:.6g} Mpc |",
        f"| resolves sigma8 | {calibration.resolves_radius(calibration.sigma8_radius_mpc)} |",
        f"| target sigma8 | {args.target_sigma8:.6g} |",
        f"| positive sigma8 | {positive_sigma8:.6g} |",
        f"| negative sigma8 | {negative_sigma8:.6g} |",
        f"| lognormal amplitude | {amplitude:.6g} |",
        f"| sector correlation | {payload['sector_correlation']:.6g} |",
        f"| positive min | {payload['positive_min']:.6g} |",
        f"| negative min | {payload['negative_min']:.6g} |",
        f"| positive max | {payload['positive_max']:.6g} |",
        f"| negative max | {payload['negative_max']:.6g} |",
        f"| density safe | {payload['positive_density_safe'] and payload['negative_density_safe']} |",
        f"| generation time | {elapsed:.6g} s |",
        "",
        f"JSON: `{JSON_PATH}`",
        "",
        "Boundary: this fixes positivity and sigma8 for a toy lognormal IC. It is not yet a Janus-derived transfer function, not a CMB fit, and not an observational proof.",
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {JSON_PATH}")


if __name__ == "__main__":
    main()
