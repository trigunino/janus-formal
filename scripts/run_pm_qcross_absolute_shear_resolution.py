from __future__ import annotations

from argparse import ArgumentParser, Namespace
from pathlib import Path
import json

import numpy as np

from janus_lab.physical_units import minimum_grid_n_for_smoothing_radius, sigma8_radius_mpc

try:
    from scripts.run_pm_qcross_absolute_shear import build_payload as build_absolute_shear_payload
except ModuleNotFoundError:
    from run_pm_qcross_absolute_shear import build_payload as build_absolute_shear_payload


REPORT_PATH = Path("outputs/reports/pm_qcross_absolute_shear_resolution.md")
JSON_PATH = Path("outputs/reports/pm_qcross_absolute_shear_resolution.json")


def parse_int_list(text: str) -> list[int]:
    values = [int(item.strip()) for item in text.split(",") if item.strip()]
    if not values:
        raise ValueError("grid list must not be empty.")
    if any(value <= 0 for value in values):
        raise ValueError("grid values must be positive.")
    return values


def parse_args():
    parser = ArgumentParser()
    parser.add_argument("--grids", default="32,48,64")
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
    parser.add_argument("--output-tag", default="")
    return parser.parse_args()


def tagged_path(path: Path, tag: str) -> Path:
    if not tag:
        return path
    safe = tag.replace("-", "_")
    return path.with_name(f"{path.stem}_{safe}{path.suffix}")


def _row_from_payload(payload: dict, previous: dict | None) -> dict:
    shear = float(payload["shear_abs_rms"])
    previous_shear = None if previous is None else float(previous["shear_abs_rms"])
    relative_change = None
    if previous_shear is not None and previous_shear != 0.0:
        relative_change = abs(shear - previous_shear) / abs(previous_shear)
    return {
        "grid": int(payload["grid"]),
        "particles": int(payload["particle_count"]),
        "kappa_abs_rms": float(payload["kappa_abs_rms"]),
        "shear_abs_rms": shear,
        "first_shear_power": float(payload["first_shear_power"]),
        "shear_power_bands": payload["shear_power_bands"],
        "speed_max_km_s": float(payload["source_metrics"]["speed_max_km_s"]),
        "relative_shear_change_from_previous": relative_change,
        "generation_seconds": float(payload["generation_seconds"]),
        "finite": bool(payload["finite"]),
        "valid": True,
        "error": "",
    }


def _invalid_row(grid: int, error: Exception) -> dict:
    return {
        "grid": int(grid),
        "particles": 0,
        "kappa_abs_rms": None,
        "shear_abs_rms": None,
        "first_shear_power": None,
        "shear_power_bands": [],
        "speed_max_km_s": None,
        "relative_shear_change_from_previous": None,
        "generation_seconds": None,
        "finite": False,
        "valid": False,
        "error": str(error),
    }


def build_payload(args) -> dict:
    grids = parse_int_list(args.grids)
    rows = []
    previous_payload = None
    for grid in grids:
        try:
            payload = build_absolute_shear_payload(
                Namespace(
                    grid=grid,
                    steps=args.steps,
                    dt=args.dt,
                    gravity_scale=args.gravity_scale,
                    box_size_mpc=args.box_size_mpc,
                    h0=args.h0,
                    omega_abs=args.omega_abs,
                    q0=args.q0,
                    source_redshifts=args.source_redshifts,
                    source_weights=args.source_weights,
                    axis=args.axis,
                    seed=args.seed,
                    shape_amplitude=args.shape_amplitude,
                    displacement_scale=args.displacement_scale,
                    ic_family=args.ic_family,
                    mass_normalization=args.mass_normalization,
                )
            )
            rows.append(_row_from_payload(payload, previous_payload))
            previous_payload = payload
        except ValueError as exc:
            rows.append(_invalid_row(grid, exc))
            previous_payload = None
    required_grid = minimum_grid_n_for_smoothing_radius(
        args.box_size_mpc,
        sigma8_radius_mpc(args.h0),
        cells_per_radius=2.0,
    )
    finite = all(row["finite"] for row in rows)
    relative_changes = [
        row["relative_shear_change_from_previous"]
        for row in rows
        if row["relative_shear_change_from_previous"] is not None
    ]
    return {
        "description": "Resolution convergence diagnostic for PM Q_cross absolute shear.",
        "run_settings": {
            "ic_family": args.ic_family,
            "displacement_scale": args.displacement_scale,
            "shape_amplitude": args.shape_amplitude,
            "steps": args.steps,
            "dt": args.dt,
            "gravity_scale": args.gravity_scale,
            "box_size_mpc": args.box_size_mpc,
            "h0": args.h0,
            "mass_normalization": args.mass_normalization,
        },
        "grids": grids,
        "required_grid_for_sigma8_radius": required_grid,
        "max_grid": max(grids),
        "meets_sigma8_resolution": max(grids) >= required_grid,
        "max_relative_shear_change": max(relative_changes) if relative_changes else None,
        "finite": finite,
        "valid_count": sum(1 for row in rows if row["valid"]),
        "invalid_count": sum(1 for row in rows if not row["valid"]),
        "rows": rows,
        "boundary": (
            "Resolution diagnostic only. Passing this does not replace the tensor derivation "
            "or survey likelihood; failing the sigma8 grid requirement keeps final S8 blocked."
        ),
    }


def main() -> None:
    args = parse_args()
    report_path = tagged_path(REPORT_PATH, args.output_tag)
    json_path = tagged_path(JSON_PATH, args.output_tag)
    report_path.parent.mkdir(parents=True, exist_ok=True)
    payload = build_payload(args)
    json_path.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# PM Q_cross Absolute Shear Resolution",
        "",
        payload["description"],
        "",
        "| metric | value |",
        "|---|---:|",
        f"| required grid for sigma8 radius | {payload['required_grid_for_sigma8_radius']} |",
        f"| max tested grid | {payload['max_grid']} |",
        f"| meets sigma8 resolution | {payload['meets_sigma8_resolution']} |",
        f"| max relative shear change | {payload['max_relative_shear_change']} |",
        f"| finite | {payload['finite']} |",
        "",
        "| grid | shear RMS | relative change | first shear power | speed max km/s | seconds |",
        "|---:|---:|---:|---:|---:|---:|",
    ]
    for row in payload["rows"]:
        change = row["relative_shear_change_from_previous"]
        change_text = "" if change is None else f"{change:.6g}"
        shear_text = "" if row["shear_abs_rms"] is None else f"{row['shear_abs_rms']:.9g}"
        power_text = (
            "" if row["first_shear_power"] is None else f"{row['first_shear_power']:.9g}"
        )
        seconds_text = (
            "" if row["generation_seconds"] is None else f"{row['generation_seconds']:.6g}"
        )
        speed_text = "" if row["speed_max_km_s"] is None else f"{row['speed_max_km_s']:.9g}"
        lines.append(
            f"| {row['grid']} | {shear_text} | {change_text} | "
            f"{power_text} | {speed_text} | {seconds_text} |"
        )
    lines.extend(["", payload["boundary"], ""])
    report_path.write_text("\n".join(lines), encoding="utf-8")
    print(f"Wrote {report_path}")
    print(f"Wrote {json_path}")


if __name__ == "__main__":
    main()
