from __future__ import annotations

from pathlib import Path

import numpy as np

from janus_lab.particle_mesh import (
    leapfrog_particle_mesh_step,
    mean_pairwise_periodic_distance,
    periodic_distance,
)
from janus_lab.signed_sector import BodyState, Sector


REPORT_PATH = Path("outputs/reports/segregation_controls.md")
CSV_PATH = Path("outputs/reports/segregation_controls.csv")


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


def group_metrics(
    bodies: list[BodyState],
    labels: list[str],
    box_size: float,
) -> dict[str, float]:
    left = [body.position for body, label in zip(bodies, labels) if label == "left"]
    right = [body.position for body, label in zip(bodies, labels) if label == "right"]
    left_internal = mean_pairwise_periodic_distance(left, box_size)
    right_internal = mean_pairwise_periodic_distance(right, box_size)
    cross = sum(periodic_distance(first, second, box_size) for first in left for second in right)
    cross /= len(left) * len(right)
    internal = 0.5 * (left_internal + right_internal)
    return {
        "left_internal": left_internal,
        "right_internal": right_internal,
        "cross": cross,
        "ratio": cross / internal if internal > 0.0 else 0.0,
    }


def run_mode(
    mode: str,
    steps: int = 100,
    dt: float = 0.00005,
    grid_shape: tuple[int, int] = (64, 64),
    box_size: float = 1.0,
) -> dict[str, float | str]:
    bodies, labels = initial_blobs(mode)
    initial = group_metrics(bodies, labels, box_size)
    if mode != "frozen":
        for _ in range(steps):
            bodies = leapfrog_particle_mesh_step(
                bodies,
                dt=dt,
                grid_shape=grid_shape,
                box_size=box_size,
            )
    final = group_metrics(bodies, labels, box_size)
    return {
        "mode": mode,
        "initial_cross": initial["cross"],
        "final_cross": final["cross"],
        "delta_cross": final["cross"] - initial["cross"],
        "initial_ratio": initial["ratio"],
        "final_ratio": final["ratio"],
        "delta_ratio": final["ratio"] - initial["ratio"],
        "delta_left_internal": final["left_internal"] - initial["left_internal"],
        "delta_right_internal": final["right_internal"] - initial["right_internal"],
    }


def main() -> None:
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    rows = [run_mode(mode) for mode in ("janus", "all_attractive", "frozen")]

    with CSV_PATH.open("w", encoding="utf-8") as handle:
        handle.write(
            "mode,initial_cross,final_cross,delta_cross,initial_ratio,"
            "final_ratio,delta_ratio,delta_left_internal,delta_right_internal\n"
        )
        for row in rows:
            handle.write(
                f"{row['mode']},{row['initial_cross']:.10g},{row['final_cross']:.10g},"
                f"{row['delta_cross']:.10g},{row['initial_ratio']:.10g},"
                f"{row['final_ratio']:.10g},{row['delta_ratio']:.10g},"
                f"{row['delta_left_internal']:.10g},{row['delta_right_internal']:.10g}\n"
            )

    lines = [
        "# Segregation Control Comparison",
        "",
        "Same two labelled blobs under Janus, all-attractive and frozen controls.",
        "",
        "| mode | delta cross distance | delta ratio | delta left internal | delta right internal | reading |",
        "|---|---:|---:|---:|---:|---|",
    ]
    for row in rows:
        delta_cross = float(row["delta_cross"])
        reading = (
            "groups separate"
            if delta_cross > 0.0
            else "groups approach"
            if delta_cross < 0.0
            else "unchanged"
        )
        lines.append(
            f"| {row['mode']} | {delta_cross:.6g} | {row['delta_ratio']:.6g} | "
            f"{row['delta_left_internal']:.6g} | {row['delta_right_internal']:.6g} | "
            f"{reading} |"
        )
    lines.extend(
        [
            "",
            f"CSV: `{CSV_PATH}`",
            "",
            "Boundary: this is a numerical control only. The all-attractive case is not a Janus physical claim; it is a baseline to isolate the sign effect.",
            "",
        ]
    )
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {CSV_PATH}")


if __name__ == "__main__":
    main()
