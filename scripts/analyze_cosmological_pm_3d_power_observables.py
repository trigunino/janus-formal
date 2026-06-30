from __future__ import annotations

from pathlib import Path
import json

import numpy as np

from janus_lab.cosmological_pm import scale_factor_sequence
from janus_lab.cosmological_pm_3d import run_cosmological_pm_3d
from janus_lab.field_statistics import (
    density_contrast,
    radial_power_spectrum_3d,
    signed_sector_contrast,
)
from janus_lab.initial_conditions import (
    paired_sector_contrasts_3d,
    two_sector_lattice_initial_conditions_3d,
)
from janus_lab.models import JanusExpansion
from janus_lab.particle_mesh_3d import particle_mesh_fields_3d


REPORT_PATH = Path("outputs/reports/cosmological_pm_3d_power_observables.md")
CSV_PATH = Path("outputs/reports/cosmological_pm_3d_power_observables.csv")
JSON_PATH = Path("outputs/reports/cosmological_pm_3d_power_observables.json")


def run_gaussian_state():
    grid_shape = (8, 8, 8)
    box_size = 1.0
    fields = paired_sector_contrasts_3d(
        grid_shape,
        box_size,
        seed=20260619,
        target_rms=0.05,
        spectral_index=1.0,
        anti_correlation=1.0,
    )
    bodies = two_sector_lattice_initial_conditions_3d(
        fields,
        box_size=box_size,
        displacement_scale=0.1,
    )
    steps = 30
    scale_factors = scale_factor_sequence(0.5, 1.0, steps)
    expansion_rates = np.asarray(
        JanusExpansion.from_q0(-0.087).e(1.0 / scale_factors - 1.0),
        dtype=float,
    )
    history = run_cosmological_pm_3d(
        bodies,
        dt=0.0001,
        scale_factors=scale_factors,
        expansion_rates=expansion_rates,
        grid_shape=grid_shape,
        box_size=box_size,
        gravity_scale=0.5,
        hubble_drag=2.0,
    )
    return history[0], history[-1], grid_shape, box_size


def fields_for_power(bodies, grid_shape: tuple[int, int, int], box_size: float):
    fields = particle_mesh_fields_3d(bodies, grid_shape=grid_shape, box_size=box_size)
    return {
        "positive": density_contrast(fields.positive_density_abs),
        "negative": density_contrast(fields.negative_density_abs),
        "signed": signed_sector_contrast(fields.positive_density_abs, fields.negative_density_abs),
    }


def main() -> None:
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    initial_bodies, final_bodies, grid_shape, box_size = run_gaussian_state()
    initial_fields = fields_for_power(initial_bodies, grid_shape, box_size)
    final_fields = fields_for_power(final_bodies, grid_shape, box_size)
    bin_edges = 2.0 * np.pi * np.asarray([0.5, 1.5, 2.5, 4.5, 8.5])

    rows = []
    for field_name in ("positive", "negative", "signed"):
        initial_spectrum = radial_power_spectrum_3d(
            initial_fields[field_name],
            box_size=box_size,
            bin_edges=bin_edges,
        )
        final_spectrum = radial_power_spectrum_3d(
            final_fields[field_name],
            box_size=box_size,
            bin_edges=bin_edges,
        )
        for index, (k_center, initial_power, final_power, count) in enumerate(
            zip(
                initial_spectrum.k_centers,
                initial_spectrum.power,
                final_spectrum.power,
                final_spectrum.mode_counts,
            )
        ):
            growth_ratio = final_power / initial_power if initial_power > 0.0 else float("inf")
            rows.append(
                {
                    "field": field_name,
                    "bin": index,
                    "k_center": float(k_center),
                    "initial_power": float(initial_power),
                    "final_power": float(final_power),
                    "growth_ratio": float(growth_ratio),
                    "mode_count": int(count),
                }
            )

    with CSV_PATH.open("w", encoding="utf-8") as handle:
        handle.write("field,bin,k_center,initial_power,final_power,growth_ratio,mode_count\n")
        for row in rows:
            handle.write(
                f"{row['field']},{row['bin']},{row['k_center']:.10g},"
                f"{row['initial_power']:.10g},{row['final_power']:.10g},"
                f"{row['growth_ratio']:.10g},{row['mode_count']}\n"
            )

    signed_rows = [row for row in rows if row["field"] == "signed"]
    payload = {
        "description": "Internal 3D band-power observables from the Gaussian-IC PM prototype.",
        "parameters": {
            "grid_shape": list(grid_shape),
            "box_size": box_size,
            "seed": 20260619,
            "target_rms": 0.05,
            "spectral_index": 1.0,
            "displacement_scale": 0.1,
            "q0": -0.087,
            "steps": 30,
            "dt": 0.0001,
            "gravity_scale": 0.5,
        },
        "signed_power_growth": [
            {
                "bin": row["bin"],
                "k_center": row["k_center"],
                "initial_power": row["initial_power"],
                "final_power": row["final_power"],
                "growth_ratio": row["growth_ratio"],
                "mode_count": row["mode_count"],
            }
            for row in signed_rows
        ],
        "boundary": "Prototype internal 3D observables only; not survey-calibrated.",
    }
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")

    lines = [
        "# Cosmological PM 3D Power Observables",
        "",
        "Internal 3D structure-observable export for the Gaussian-IC PM prototype.",
        "",
        "| signed k bin | modes | initial power | final power | growth ratio |",
        "|---:|---:|---:|---:|---:|",
    ]
    for row in signed_rows:
        lines.append(
            f"| {row['bin']} | {row['mode_count']} | {row['initial_power']:.6g} | "
            f"{row['final_power']:.6g} | {row['growth_ratio']:.6g} |"
        )
    lines.extend(
        [
            "",
            f"CSV: `{CSV_PATH}`",
            f"JSON: `{JSON_PATH}`",
            "",
            "Boundary: these are internal 3D band-power observables from a prototype simulation. They are not survey-calibrated and are not yet comparable to physical Mpc-scale spectra without units, transfer functions and normalization.",
            "",
        ]
    )
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {CSV_PATH}")
    print(f"Wrote {JSON_PATH}")


if __name__ == "__main__":
    main()
