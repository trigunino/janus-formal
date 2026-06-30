from __future__ import annotations

from pathlib import Path

import numpy as np

from janus_lab.cosmological_pm import run_cosmological_pm, scale_factor_sequence
from janus_lab.field_statistics import density_field_summary
from janus_lab.initial_conditions import (
    paired_sector_contrasts,
    two_sector_lattice_initial_conditions,
)
from janus_lab.models import JanusExpansion
from janus_lab.particle_mesh import particle_mesh_fields


REPORT_PATH = Path("outputs/reports/gaussian_ic_seed_robustness.md")
CSV_PATH = Path("outputs/reports/gaussian_ic_seed_robustness.csv")


def field_summary(bodies):
    fields = particle_mesh_fields(bodies, grid_shape=(32, 32), box_size=1.0)
    return density_field_summary(fields.positive_density_abs, fields.negative_density_abs)


def run_seed(seed: int) -> dict[str, float]:
    contrast_fields = paired_sector_contrasts(
        (32, 32),
        1.0,
        seed=seed,
        target_rms=0.05,
        spectral_index=1.0,
        anti_correlation=1.0,
    )
    bodies = two_sector_lattice_initial_conditions(
        contrast_fields,
        box_size=1.0,
        displacement_scale=0.1,
    )
    steps = 50
    scale_factors = scale_factor_sequence(0.5, 1.0, steps)
    expansion_rates = np.asarray(
        JanusExpansion.from_q0(-0.087).e(1.0 / scale_factors - 1.0),
        dtype=float,
    )
    history = run_cosmological_pm(
        bodies,
        dt=0.0001,
        scale_factors=scale_factors,
        expansion_rates=expansion_rates,
        grid_shape=(32, 32),
        box_size=1.0,
        gravity_scale=0.5,
        hubble_drag=2.0,
    )
    initial = field_summary(history[0])
    final = field_summary(history[-1])
    return {
        "seed": float(seed),
        "delta_signed_rms": final.signed_contrast_rms - initial.signed_contrast_rms,
        "initial_correlation": initial.sector_correlation,
        "final_correlation": final.sector_correlation,
        "delta_correlation": final.sector_correlation - initial.sector_correlation,
    }


def main() -> None:
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    rows = [run_seed(seed) for seed in (11, 22, 33, 44, 55)]
    passed = [row for row in rows if row["delta_signed_rms"] > 0.0]

    with CSV_PATH.open("w", encoding="utf-8") as handle:
        handle.write(
            "seed,delta_signed_rms,initial_correlation,final_correlation,delta_correlation\n"
        )
        for row in rows:
            handle.write(
                f"{int(row['seed'])},{row['delta_signed_rms']:.10g},"
                f"{row['initial_correlation']:.10g},{row['final_correlation']:.10g},"
                f"{row['delta_correlation']:.10g}\n"
            )

    lines = [
        "# Gaussian IC Seed Robustness",
        "",
        "Same Gaussian-IC comoving PM prototype across independent random seeds.",
        "",
        f"Passing seeds: `{len(passed)}/{len(rows)}`.",
        "",
        "| seed | delta signed RMS | initial correlation | final correlation |",
        "|---:|---:|---:|---:|",
    ]
    for row in rows:
        lines.append(
            f"| {int(row['seed'])} | {row['delta_signed_rms']:.6g} | "
            f"{row['initial_correlation']:.6g} | {row['final_correlation']:.6g} |"
        )
    lines.extend(
        [
            "",
            f"CSV: `{CSV_PATH}`",
            "",
            "Boundary: seed robustness only. These ICs are still prototype Gaussian fields, not CMB-normalized or transfer-function calibrated.",
            "",
        ]
    )
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {CSV_PATH}")


if __name__ == "__main__":
    main()
