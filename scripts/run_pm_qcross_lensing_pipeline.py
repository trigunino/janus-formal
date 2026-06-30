from __future__ import annotations

from argparse import ArgumentParser
from pathlib import Path
import csv
import json
import time

import numpy as np

from janus_lab.cosmological_pm import scale_factor_sequence
from janus_lab.models import JanusExpansion
from janus_lab.particle_mesh_3d_vectorized import (
    cosmological_pm_step_3d_vectorized,
    deposit_cloud_in_cell_3d_vectorized,
    deposit_sector_cloud_in_cell_3d_vectorized,
    estimate_vectorized_pm_memory_bytes,
)
from janus_lab.physical_units import hubble_time_gyr

try:
    from scripts.diagnose_pm_state_qcross import (
        DEFAULT_PHOTON_DIRECTION,
        _stats,
        build_demo_state,
        negative_qcross_from_state,
    )
except ModuleNotFoundError:
    from diagnose_pm_state_qcross import (
        DEFAULT_PHOTON_DIRECTION,
        _stats,
        build_demo_state,
        negative_qcross_from_state,
    )


REPORT_PATH = Path("outputs/reports/pm_qcross_lensing_pipeline.md")
CSV_PATH = Path("outputs/reports/pm_qcross_lensing_pipeline.csv")
JSON_PATH = Path("outputs/reports/pm_qcross_lensing_pipeline.json")


def gb(value: int) -> float:
    return value / 1024.0**3


def qcross_source_metrics(
    state,
    *,
    grid_shape: tuple[int, int, int],
    box_size: float,
    box_size_mpc: float,
    time_unit_gyr: float,
) -> dict[str, float]:
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
    equal_source = positive_density - negative_density
    qcross_source = positive_density - negative_qcross_density
    centered_equal = equal_source - float(np.mean(equal_source))
    centered_qcross = qcross_source - float(np.mean(qcross_source))
    delta = centered_qcross - centered_equal
    speed = np.linalg.norm(velocities_km_s, axis=1)
    return {
        "qcross_min": _stats(q_cross)["min"],
        "qcross_mean": _stats(q_cross)["mean"],
        "qcross_max": _stats(q_cross)["max"],
        "speed_max_km_s": _stats(speed)["max"],
        "source_rms": float(np.sqrt(np.mean(centered_qcross**2))),
        "source_delta_rms": float(np.sqrt(np.mean(delta**2))),
        "finite": bool(np.isfinite(centered_qcross).all() and np.isfinite(q_cross).all()),
    }


def parse_args():
    parser = ArgumentParser()
    parser.add_argument("--grid", type=int, default=16)
    parser.add_argument("--steps", type=int, default=4)
    parser.add_argument("--dt", type=float, default=0.0001)
    parser.add_argument("--gravity-scale", type=float, default=0.5)
    parser.add_argument("--box-size-mpc", type=float, default=1000.0)
    parser.add_argument("--h0", type=float, default=70.0)
    parser.add_argument("--time-unit-gyr", type=float, default=None)
    return parser.parse_args()


def build_payload(args) -> dict:
    if args.grid <= 0:
        raise ValueError("--grid must be positive.")
    if args.steps <= 1:
        raise ValueError("--steps must be greater than one.")
    grid_shape = (args.grid, args.grid, args.grid)
    time_unit_gyr = (
        hubble_time_gyr(args.h0) if args.time_unit_gyr is None else args.time_unit_gyr
    )
    state = build_demo_state(grid_shape=grid_shape, box_size=1.0)
    particle_count = int(len(state.positions))
    estimated_gb = gb(estimate_vectorized_pm_memory_bytes(grid_shape, particle_count))

    scale_factors = scale_factor_sequence(0.5, 1.0, args.steps)
    expansion_rates = np.asarray(
        JanusExpansion.from_q0(-0.087).e(1.0 / scale_factors - 1.0),
        dtype=float,
    )
    rows = []
    total_start = time.perf_counter()
    for step, (scale_factor, expansion_rate) in enumerate(
        zip(scale_factors[:-1], expansion_rates[:-1]),
        start=1,
    ):
        step_start = time.perf_counter()
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
        metrics = qcross_source_metrics(
            state,
            grid_shape=grid_shape,
            box_size=1.0,
            box_size_mpc=args.box_size_mpc,
            time_unit_gyr=time_unit_gyr,
        )
        rows.append(
            {
                "step": step,
                "scale_factor": float(scale_factor),
                "expansion_rate": float(expansion_rate),
                "seconds": time.perf_counter() - step_start,
                **metrics,
            }
        )
    total_seconds = time.perf_counter() - total_start
    return {
        "description": "Short vectorized PM evolution with velocity-derived Q_cross source diagnostics.",
        "grid": args.grid,
        "steps_requested": args.steps,
        "steps_completed": len(rows),
        "particle_count": particle_count,
        "estimated_core_memory_gb": estimated_gb,
        "box_size_mpc": args.box_size_mpc,
        "h0_km_s_mpc": args.h0,
        "time_unit_gyr": time_unit_gyr,
        "time_unit_basis": "H0^-1" if args.time_unit_gyr is None else "explicit",
        "dt": args.dt,
        "gravity_scale": args.gravity_scale,
        "total_seconds": total_seconds,
        "finite": all(row["finite"] for row in rows),
        "rows": rows,
        "boundary": (
            "Diagnostic pipeline only. It advances PM state, computes Q_cross from calibrated "
            "negative velocities, then forms rho_plus - Q_cross rho_minus. It is not S8, "
            "not a survey likelihood, and not a final tensor derivation."
        ),
    }


def main() -> None:
    args = parse_args()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    payload = build_payload(args)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")

    with CSV_PATH.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(payload["rows"][0].keys()))
        writer.writeheader()
        writer.writerows(payload["rows"])

    lines = [
        "# PM Q_cross Lensing Pipeline",
        "",
        payload["description"],
        "",
        "| metric | value |",
        "|---|---:|",
        f"| grid | {payload['grid']}^3 |",
        f"| particles | {payload['particle_count']} |",
        f"| estimated core memory | {payload['estimated_core_memory_gb']:.6g} GB |",
        f"| H0 | {payload['h0_km_s_mpc']:.6g} km/s/Mpc |",
        f"| time unit | {payload['time_unit_gyr']:.6g} Gyr |",
        f"| time unit basis | {payload['time_unit_basis']} |",
        f"| completed steps | {payload['steps_completed']} |",
        f"| total seconds | {payload['total_seconds']:.6g} |",
        f"| finite | {payload['finite']} |",
        "",
        "| step | seconds | Q_cross mean | speed max km/s | source rms | delta rms |",
        "|---:|---:|---:|---:|---:|---:|",
    ]
    for row in payload["rows"]:
        lines.append(
            f"| {row['step']} | {row['seconds']:.6g} | {row['qcross_mean']:.9g} | "
            f"{row['speed_max_km_s']:.9g} | {row['source_rms']:.9g} | "
            f"{row['source_delta_rms']:.9g} |"
        )
    lines.extend(["", payload["boundary"], f"CSV: `{CSV_PATH}`", ""])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {CSV_PATH}")
    print(f"Wrote {JSON_PATH}")


if __name__ == "__main__":
    main()
