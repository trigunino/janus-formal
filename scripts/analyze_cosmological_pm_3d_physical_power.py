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
from janus_lab.physical_units import PhysicalBoxCalibration


REPORT_PATH = Path("outputs/reports/cosmological_pm_3d_physical_power.md")
CSV_PATH = Path("outputs/reports/cosmological_pm_3d_physical_power.csv")
JSON_PATH = Path("outputs/reports/cosmological_pm_3d_physical_power.json")


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
    return history[0], history[-1], grid_shape


def fields_for_power(bodies, grid_shape: tuple[int, int, int]):
    fields = particle_mesh_fields_3d(bodies, grid_shape=grid_shape, box_size=1.0)
    return {
        "positive": density_contrast(fields.positive_density_abs),
        "negative": density_contrast(fields.negative_density_abs),
        "signed": signed_sector_contrast(fields.positive_density_abs, fields.negative_density_abs),
    }


def mean_physical_power_mpc3(power_sum: float, mode_count: int, volume_mpc3: float) -> float:
    if mode_count <= 0:
        return float("nan")
    return float(volume_mpc3 * power_sum / mode_count)


def main() -> None:
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    initial_bodies, final_bodies, grid_shape = run_gaussian_state()
    calibration = PhysicalBoxCalibration.from_total_absolute_omega(
        box_size_mpc=1000.0,
        grid_shape=grid_shape,
        h0_km_s_mpc=70.0,
        omega_abs=0.315,
        positive_fraction=0.5,
    )
    initial_fields = fields_for_power(initial_bodies, grid_shape)
    final_fields = fields_for_power(final_bodies, grid_shape)
    bin_edges = calibration.fundamental_mode_inv_mpc * np.asarray(
        [0.5, 1.5, 2.5, 4.5, 8.5],
        dtype=float,
    )

    rows = []
    for field_name in ("positive", "negative", "signed"):
        initial_spectrum = radial_power_spectrum_3d(
            initial_fields[field_name],
            box_size=calibration.box_size_mpc,
            bin_edges=bin_edges,
        )
        final_spectrum = radial_power_spectrum_3d(
            final_fields[field_name],
            box_size=calibration.box_size_mpc,
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
            initial_mpc3 = mean_physical_power_mpc3(
                float(initial_power),
                int(count),
                calibration.volume_mpc3,
            )
            final_mpc3 = mean_physical_power_mpc3(
                float(final_power),
                int(count),
                calibration.volume_mpc3,
            )
            rows.append(
                {
                    "field": field_name,
                    "bin": index,
                    "k_center_inv_mpc": float(k_center),
                    "mode_count": int(count),
                    "initial_power_mpc3": initial_mpc3,
                    "final_power_mpc3": final_mpc3,
                    "growth_ratio": final_mpc3 / initial_mpc3 if initial_mpc3 > 0.0 else float("inf"),
                }
            )

    with CSV_PATH.open("w", encoding="utf-8") as handle:
        handle.write(
            "field,bin,k_center_inv_mpc,mode_count,initial_power_mpc3,"
            "final_power_mpc3,growth_ratio\n"
        )
        for row in rows:
            handle.write(
                f"{row['field']},{row['bin']},{row['k_center_inv_mpc']:.10g},"
                f"{row['mode_count']},{row['initial_power_mpc3']:.10g},"
                f"{row['final_power_mpc3']:.10g},{row['growth_ratio']:.10g}\n"
            )

    signed_rows = [row for row in rows if row["field"] == "signed"]
    payload = {
        "description": "Physical-scale 3D band powers from the dimensionless Gaussian-IC PM prototype.",
        "calibration": {
            "box_size_mpc": calibration.box_size_mpc,
            "grid_shape": list(calibration.grid_shape),
            "h0_km_s_mpc": calibration.h0_km_s_mpc,
            "omega_abs": calibration.positive_omega_abs + calibration.negative_omega_abs,
            "positive_fraction": 0.5,
            "cell_size_mpc": list(calibration.cell_size_mpc),
        },
        "signed_power_growth": [
            {
                "bin": row["bin"],
                "k_center_inv_mpc": row["k_center_inv_mpc"],
                "mode_count": row["mode_count"],
                "initial_power_mpc3": row["initial_power_mpc3"],
                "final_power_mpc3": row["final_power_mpc3"],
                "growth_ratio": row["growth_ratio"],
            }
            for row in signed_rows
        ],
        "boundary": "Physical k/P scaling only; the PM dynamics remain dimensionless.",
    }
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")

    lines = [
        "# Cosmological PM 3D Physical Power",
        "",
        "Physical-scale band powers for the Gaussian-IC 3D PM prototype.",
        "",
        "| signed bin | k center [1/Mpc] | modes | initial P [Mpc^3] | final P [Mpc^3] | growth |",
        "|---:|---:|---:|---:|---:|---:|",
    ]
    for row in signed_rows:
        lines.append(
            f"| {row['bin']} | {row['k_center_inv_mpc']:.6g} | {row['mode_count']} | "
            f"{row['initial_power_mpc3']:.6g} | {row['final_power_mpc3']:.6g} | "
            f"{row['growth_ratio']:.6g} |"
        )
    lines.extend(
        [
            "",
            f"Box: `{calibration.box_size_mpc:.6g} Mpc`, cell: `{calibration.cell_size_mpc[0]:.6g} Mpc`.",
            f"CSV: `{CSV_PATH}`",
            f"JSON: `{JSON_PATH}`",
            "",
            "Boundary: this only maps the existing dimensionless run onto physical k/P units. It is not yet a physical N-body run, not CMB-normalized, and not survey-calibrated.",
            "",
        ]
    )
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {CSV_PATH}")
    print(f"Wrote {JSON_PATH}")


if __name__ == "__main__":
    main()
