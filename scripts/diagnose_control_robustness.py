from __future__ import annotations

from pathlib import Path

import numpy as np

from janus_lab.particle_mesh import (
    leapfrog_particle_mesh_step,
    mean_pairwise_periodic_distance,
    periodic_distance,
)
from janus_lab.signed_sector import BodyState, Sector


REPORT_PATH = Path("outputs/reports/control_robustness.md")
CSV_PATH = Path("outputs/reports/control_robustness.csv")


def initial_blobs(mode: str) -> tuple[list[BodyState], list[str]]:
    bodies: list[BodyState] = []
    labels: list[str] = []
    offsets = (-0.03, -0.01, 0.01, 0.03)
    for dx in offsets:
        for dy in offsets:
            bodies.append(
                BodyState(np.asarray([0.42 + dx, 0.5 + dy]), np.zeros(2), 1.0, Sector.POSITIVE)
            )
            labels.append("left")
            right_sector = Sector.NEGATIVE if mode == "janus" else Sector.POSITIVE
            bodies.append(
                BodyState(np.asarray([0.58 + dx, 0.5 + dy]), np.zeros(2), 1.0, right_sector)
            )
            labels.append("right")
    return bodies, labels


def cross_distance(bodies: list[BodyState], labels: list[str], box_size: float) -> float:
    left = [body.position for body, label in zip(bodies, labels) if label == "left"]
    right = [body.position for body, label in zip(bodies, labels) if label == "right"]
    return sum(periodic_distance(first, second, box_size) for first in left for second in right) / (
        len(left) * len(right)
    )


def internal_distance(bodies: list[BodyState], labels: list[str], box_size: float) -> float:
    left = [body.position for body, label in zip(bodies, labels) if label == "left"]
    right = [body.position for body, label in zip(bodies, labels) if label == "right"]
    return 0.5 * (
        mean_pairwise_periodic_distance(left, box_size)
        + mean_pairwise_periodic_distance(right, box_size)
    )


def run_case(mode: str, grid_n: int, dt: float, total_time: float = 0.005) -> dict[str, float | str]:
    bodies, labels = initial_blobs(mode)
    grid_shape = (grid_n, grid_n)
    box_size = 1.0
    steps = int(round(total_time / dt))
    initial_cross = cross_distance(bodies, labels, box_size)
    initial_internal = internal_distance(bodies, labels, box_size)
    for _ in range(steps):
        bodies = leapfrog_particle_mesh_step(
            bodies,
            dt=dt,
            grid_shape=grid_shape,
            box_size=box_size,
        )
    final_cross = cross_distance(bodies, labels, box_size)
    final_internal = internal_distance(bodies, labels, box_size)
    return {
        "mode": mode,
        "grid_n": float(grid_n),
        "dt": dt,
        "steps": float(steps),
        "delta_cross": final_cross - initial_cross,
        "delta_internal": final_internal - initial_internal,
    }


def main() -> None:
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    rows = [
        run_case(mode, grid_n, dt)
        for mode in ("janus", "all_attractive")
        for grid_n in (32, 48, 64)
        for dt in (0.000025, 0.00005, 0.0001)
    ]
    passed = [
        row
        for row in rows
        if (row["mode"] == "janus" and row["delta_cross"] > 0.0)
        or (row["mode"] == "all_attractive" and row["delta_cross"] < 0.0)
    ]

    with CSV_PATH.open("w", encoding="utf-8") as handle:
        handle.write("mode,grid_n,dt,steps,delta_cross,delta_internal\n")
        for row in rows:
            handle.write(
                f"{row['mode']},{int(row['grid_n'])},{row['dt']:.10g},"
                f"{int(row['steps'])},{row['delta_cross']:.10g},"
                f"{row['delta_internal']:.10g}\n"
            )

    lines = [
        "# Control Robustness Diagnostic",
        "",
        "Janus and all-attractive labelled-blob controls across grid and time-step choices.",
        "",
        f"Passing cases: `{len(passed)}/{len(rows)}`.",
        "",
        "| mode | grid n | dt | delta cross | delta internal | sign check |",
        "|---|---:|---:|---:|---:|---|",
    ]
    for row in rows:
        expected = "separate" if row["mode"] == "janus" else "approach"
        ok = (
            row["delta_cross"] > 0.0 if row["mode"] == "janus" else row["delta_cross"] < 0.0
        )
        lines.append(
            f"| {row['mode']} | {int(row['grid_n'])} | {row['dt']:.6g} | "
            f"{row['delta_cross']:.6g} | {row['delta_internal']:.6g} | "
            f"{expected if ok else 'fail'} |"
        )
    lines.extend(
        [
            "",
            f"CSV: `{CSV_PATH}`",
            "",
            "Boundary: numerical control only. This isolates PM sign behavior; it is not an observational or cosmological validation.",
            "",
        ]
    )
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {CSV_PATH}")


if __name__ == "__main__":
    main()
