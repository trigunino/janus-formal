from __future__ import annotations

from pathlib import Path

import numpy as np

from janus_lab.particle_mesh import leapfrog_particle_mesh_step, segregation_metrics
from janus_lab.signed_sector import BodyState, Sector


REPORT_PATH = Path("outputs/reports/two_sector_segregation.md")
CSV_PATH = Path("outputs/reports/two_sector_segregation.csv")


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


def main() -> None:
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    grid_shape = (64, 64)
    box_size = 1.0
    dt = 0.00005
    steps = 100
    bodies = initial_blobs()
    rows = []

    for step in range(steps + 1):
        metrics = segregation_metrics(bodies, box_size=box_size)
        rows.append(
            {
                "step": step,
                "positive_internal": metrics.positive_internal_distance,
                "negative_internal": metrics.negative_internal_distance,
                "cross": metrics.cross_sector_distance,
                "ratio": metrics.segregation_ratio,
            }
        )
        if step < steps:
            bodies = leapfrog_particle_mesh_step(
                bodies,
                dt=dt,
                grid_shape=grid_shape,
                box_size=box_size,
            )

    with CSV_PATH.open("w", encoding="utf-8") as handle:
        handle.write(
            "step,positive_internal_distance,negative_internal_distance,"
            "cross_sector_distance,segregation_ratio\n"
        )
        for row in rows:
            handle.write(
                f"{row['step']},{row['positive_internal']:.10g},"
                f"{row['negative_internal']:.10g},{row['cross']:.10g},"
                f"{row['ratio']:.10g}\n"
            )

    initial = rows[0]
    final = rows[-1]
    lines = [
        "# Two-Sector Segregation Diagnostic",
        "",
        "Short weak-field particle-mesh run from two deterministic 16-particle blobs.",
        "",
        "| metric | initial | final | delta |",
        "|---|---:|---:|---:|",
        (
            f"| positive internal distance | {initial['positive_internal']:.6g} | "
            f"{final['positive_internal']:.6g} | "
            f"{final['positive_internal'] - initial['positive_internal']:.6g} |"
        ),
        (
            f"| negative internal distance | {initial['negative_internal']:.6g} | "
            f"{final['negative_internal']:.6g} | "
            f"{final['negative_internal'] - initial['negative_internal']:.6g} |"
        ),
        (
            f"| cross-sector distance | {initial['cross']:.6g} | {final['cross']:.6g} | "
            f"{final['cross'] - initial['cross']:.6g} |"
        ),
        (
            f"| segregation ratio | {initial['ratio']:.6g} | {final['ratio']:.6g} | "
            f"{final['ratio'] - initial['ratio']:.6g} |"
        ),
        "",
        f"Grid: `{grid_shape[0]}x{grid_shape[1]}`, steps: `{steps}`, dt: `{dt}`.",
        f"CSV: `{CSV_PATH}`",
        "",
        "Reading: same-sector attraction compacts each blob while opposite-sector repulsion increases the cross-sector distance.",
        "",
        "Boundary: this is a numerical mechanism diagnostic only. It is not a cosmological N-body simulation, not a fit, and not observational evidence.",
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {CSV_PATH}")


if __name__ == "__main__":
    main()
