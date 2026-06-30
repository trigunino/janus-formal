from __future__ import annotations

from pathlib import Path

import numpy as np

from janus_lab.cosmological_pm import run_cosmological_pm, scale_factor_sequence
from janus_lab.field_statistics import density_field_summary
from janus_lab.initial_conditions import (
    paired_sector_contrasts,
    sector_contrast_correlation,
    two_sector_lattice_initial_conditions,
)
from janus_lab.models import JanusExpansion
from janus_lab.particle_mesh import particle_mesh_fields


REPORT_PATH = Path("outputs/reports/cosmological_pm_gaussian_ic.md")
CSV_PATH = Path("outputs/reports/cosmological_pm_gaussian_ic.csv")


def field_summary_for_bodies(bodies, grid_shape: tuple[int, int], box_size: float):
    fields = particle_mesh_fields(bodies, grid_shape=grid_shape, box_size=box_size)
    return density_field_summary(fields.positive_density_abs, fields.negative_density_abs)


def main() -> None:
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    grid_shape = (32, 32)
    box_size = 1.0
    seed = 20260614
    target_rms = 0.05
    spectral_index = 1.0
    displacement_scale = 0.1
    q0 = -0.087
    steps = 50
    dt = 0.0001
    gravity_scale = 0.5

    contrast_fields = paired_sector_contrasts(
        grid_shape,
        box_size,
        seed=seed,
        target_rms=target_rms,
        spectral_index=spectral_index,
        anti_correlation=1.0,
    )
    bodies = two_sector_lattice_initial_conditions(
        contrast_fields,
        box_size=box_size,
        displacement_scale=displacement_scale,
    )
    scale_factors = scale_factor_sequence(0.5, 1.0, steps)
    redshifts = 1.0 / scale_factors - 1.0
    expansion_rates = np.asarray(JanusExpansion.from_q0(q0).e(redshifts), dtype=float)
    history = run_cosmological_pm(
        bodies,
        dt=dt,
        scale_factors=scale_factors,
        expansion_rates=expansion_rates,
        grid_shape=grid_shape,
        box_size=box_size,
        gravity_scale=gravity_scale,
        hubble_drag=2.0,
    )

    rows = []
    for step, (state, scale_factor, redshift, expansion_rate) in enumerate(
        zip(history, scale_factors, redshifts, expansion_rates)
    ):
        summary = field_summary_for_bodies(state, grid_shape, box_size)
        rows.append(
            {
                "step": step,
                "scale_factor": float(scale_factor),
                "redshift": float(redshift),
                "expansion_rate": float(expansion_rate),
                "positive_rms": summary.positive_contrast_rms,
                "negative_rms": summary.negative_contrast_rms,
                "sector_correlation": summary.sector_correlation,
                "signed_rms": summary.signed_contrast_rms,
            }
        )

    with CSV_PATH.open("w", encoding="utf-8") as handle:
        handle.write(
            "step,scale_factor,redshift,E,positive_contrast_rms,"
            "negative_contrast_rms,sector_correlation,signed_contrast_rms\n"
        )
        for row in rows:
            handle.write(
                f"{row['step']},{row['scale_factor']:.10g},{row['redshift']:.10g},"
                f"{row['expansion_rate']:.10g},{row['positive_rms']:.10g},"
                f"{row['negative_rms']:.10g},{row['sector_correlation']:.10g},"
                f"{row['signed_rms']:.10g}\n"
            )

    initial = rows[0]
    final = rows[-1]
    lines = [
        "# Cosmological PM With Gaussian IC",
        "",
        "Prototype comoving PM run from reproducible anti-correlated Gaussian two-sector initial conditions.",
        "",
        "| metric | initial | final | delta |",
        "|---|---:|---:|---:|",
        (
            f"| signed contrast RMS | {initial['signed_rms']:.6g} | "
            f"{final['signed_rms']:.6g} | "
            f"{final['signed_rms'] - initial['signed_rms']:.6g} |"
        ),
        (
            f"| sector correlation | {initial['sector_correlation']:.6g} | "
            f"{final['sector_correlation']:.6g} | "
            f"{final['sector_correlation'] - initial['sector_correlation']:.6g} |"
        ),
        (
            f"| positive contrast RMS | {initial['positive_rms']:.6g} | "
            f"{final['positive_rms']:.6g} | "
            f"{final['positive_rms'] - initial['positive_rms']:.6g} |"
        ),
        (
            f"| negative contrast RMS | {initial['negative_rms']:.6g} | "
            f"{final['negative_rms']:.6g} | "
            f"{final['negative_rms'] - initial['negative_rms']:.6g} |"
        ),
        "",
        f"Input field correlation: `{sector_contrast_correlation(contrast_fields):.6g}`.",
        f"Seed: `{seed}`, target input RMS: `{target_rms}`, spectral index: `{spectral_index}`.",
        f"Displacement scale: `{displacement_scale}`, gravity scale: `{gravity_scale}`.",
        f"Background: `JanusExpansion.from_q0({q0})`, `a=0.5 -> 1.0`.",
        f"CSV: `{CSV_PATH}`",
        "",
        "Boundary: Gaussian IC and displacement mapping are prototype choices. This is not CMB-normalized, not transfer-function calibrated, and not survey validated.",
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {CSV_PATH}")


if __name__ == "__main__":
    main()
