from __future__ import annotations

from pathlib import Path

import numpy as np

from janus_lab.cosmological_pm import run_cosmological_pm, scale_factor_sequence
from janus_lab.field_statistics import density_field_summary
from janus_lab.models import JanusExpansion
from janus_lab.particle_mesh import particle_mesh_fields, segregation_metrics
from janus_lab.signed_sector import BodyState, Sector


REPORT_PATH = Path("outputs/reports/cosmological_pm_prototype.md")
CSV_PATH = Path("outputs/reports/cosmological_pm_prototype.csv")


def initial_blobs() -> list[BodyState]:
    bodies: list[BodyState] = []
    offsets = (-0.03, -0.01, 0.01, 0.03)
    for dx in offsets:
        for dy in offsets:
            bodies.append(
                BodyState(np.asarray([0.42 + dx, 0.5 + dy]), np.zeros(2), 1.0, Sector.POSITIVE)
            )
            bodies.append(
                BodyState(np.asarray([0.58 + dx, 0.5 + dy]), np.zeros(2), 1.0, Sector.NEGATIVE)
            )
    return bodies


def signed_contrast_rms(
    bodies: list[BodyState],
    grid_shape: tuple[int, int],
    box_size: float,
) -> float:
    fields = particle_mesh_fields(bodies, grid_shape=grid_shape, box_size=box_size)
    return density_field_summary(
        fields.positive_density_abs,
        fields.negative_density_abs,
    ).signed_contrast_rms


def main() -> None:
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    grid_shape = (64, 64)
    box_size = 1.0
    q0 = -0.087
    steps = 100
    dt = 0.00005
    gravity_scale = 0.1
    hubble_drag = 2.0
    scale_factors = scale_factor_sequence(0.5, 1.0, steps)
    redshifts = 1.0 / scale_factors - 1.0
    expansion = JanusExpansion.from_q0(q0)
    expansion_rates = np.asarray(expansion.e(redshifts), dtype=float)
    history = run_cosmological_pm(
        initial_blobs(),
        dt=dt,
        scale_factors=scale_factors,
        expansion_rates=expansion_rates,
        grid_shape=grid_shape,
        box_size=box_size,
        gravity_scale=gravity_scale,
        hubble_drag=hubble_drag,
    )

    rows = []
    for step, (bodies, scale_factor, redshift, expansion_rate) in enumerate(
        zip(history, scale_factors, redshifts, expansion_rates)
    ):
        metrics = segregation_metrics(bodies, box_size=box_size)
        rows.append(
            {
                "step": step,
                "scale_factor": float(scale_factor),
                "redshift": float(redshift),
                "expansion_rate": float(expansion_rate),
                "cross": metrics.cross_sector_distance,
                "ratio": metrics.segregation_ratio,
                "signed_rms": signed_contrast_rms(bodies, grid_shape, box_size),
            }
        )

    with CSV_PATH.open("w", encoding="utf-8") as handle:
        handle.write(
            "step,scale_factor,redshift,E,separator_cross_distance,"
            "segregation_ratio,signed_contrast_rms\n"
        )
        for row in rows:
            handle.write(
                f"{row['step']},{row['scale_factor']:.10g},{row['redshift']:.10g},"
                f"{row['expansion_rate']:.10g},{row['cross']:.10g},"
                f"{row['ratio']:.10g},{row['signed_rms']:.10g}\n"
            )

    initial = rows[0]
    final = rows[-1]
    lines = [
        "# Cosmological PM Prototype",
        "",
        "Dimensionless comoving particle-mesh prototype using the Janus expansion background.",
        "",
        "| metric | initial | final | delta |",
        "|---|---:|---:|---:|",
        (
            f"| scale factor | {initial['scale_factor']:.6g} | "
            f"{final['scale_factor']:.6g} | "
            f"{final['scale_factor'] - initial['scale_factor']:.6g} |"
        ),
        (
            f"| redshift | {initial['redshift']:.6g} | {final['redshift']:.6g} | "
            f"{final['redshift'] - initial['redshift']:.6g} |"
        ),
        (
            f"| E(z) | {initial['expansion_rate']:.6g} | "
            f"{final['expansion_rate']:.6g} | "
            f"{final['expansion_rate'] - initial['expansion_rate']:.6g} |"
        ),
        (
            f"| cross-sector distance | {initial['cross']:.6g} | {final['cross']:.6g} | "
            f"{final['cross'] - initial['cross']:.6g} |"
        ),
        (
            f"| segregation ratio | {initial['ratio']:.6g} | {final['ratio']:.6g} | "
            f"{final['ratio'] - initial['ratio']:.6g} |"
        ),
        (
            f"| signed contrast RMS | {initial['signed_rms']:.6g} | "
            f"{final['signed_rms']:.6g} | "
            f"{final['signed_rms'] - initial['signed_rms']:.6g} |"
        ),
        "",
        f"Background: `JanusExpansion.from_q0({q0})`, `a=0.5 -> 1.0`.",
        f"Grid: `{grid_shape[0]}x{grid_shape[1]}`, steps: `{steps}`, dt: `{dt}`.",
        f"Numerical gravity scale: `{gravity_scale}`, Hubble drag coefficient: `{hubble_drag}`.",
        f"CSV: `{CSV_PATH}`",
        "",
        "Boundary: this is a prototype comoving wrapper. It is not yet a calibrated cosmological N-body code, does not include an expanding metric solver, and does not compare to survey data.",
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {CSV_PATH}")


if __name__ == "__main__":
    main()
