from __future__ import annotations

from pathlib import Path
import json

import numpy as np

from janus_lab.lensing import relative_velocity_cross_projection_from_velocities_km_s
from janus_lab.particle_mesh_3d_vectorized import create_two_sector_lattice_state_3d
from janus_lab.physical_units import pm_dimensionless_velocities_to_km_s, pm_velocity_unit_km_s


REPORT_PATH = Path("outputs/reports/pm_state_qcross.md")
JSON_PATH = Path("outputs/reports/pm_state_qcross.json")
DEFAULT_GRID_SHAPE = (2, 2, 2)
DEFAULT_BOX_SIZE = 1.0
DEFAULT_BOX_SIZE_MPC = 1000.0
DEFAULT_TIME_UNIT_GYR = 1.0
DEFAULT_PHOTON_DIRECTION = np.asarray([1.0, 0.0, 0.0])


def _stats(values: np.ndarray) -> dict[str, float]:
    arr = np.asarray(values, dtype=float)
    return {
        "min": float(np.min(arr)),
        "mean": float(np.mean(arr)),
        "max": float(np.max(arr)),
        "std": float(np.std(arr)),
    }


def build_demo_state(
    grid_shape: tuple[int, int, int] = DEFAULT_GRID_SHAPE,
    box_size: float = DEFAULT_BOX_SIZE,
):
    state = create_two_sector_lattice_state_3d(grid_shape, box_size=box_size)
    negative = state.sector_signs == -1
    positions = state.positions[negative]
    state.velocities[negative, 0] = 1.0e-4 * np.sin(2.0 * np.pi * positions[:, 1])
    state.velocities[negative, 1] = 5.0e-5 * np.cos(2.0 * np.pi * positions[:, 2])
    state.velocities[negative, 2] = 2.0e-5 * np.sin(2.0 * np.pi * positions[:, 0])
    return state


def negative_qcross_from_state(
    state,
    *,
    box_size_mpc: float = DEFAULT_BOX_SIZE_MPC,
    time_unit_gyr: float = DEFAULT_TIME_UNIT_GYR,
    photon_direction: np.ndarray = DEFAULT_PHOTON_DIRECTION,
):
    negative = state.sector_signs == -1

    negative_dimensionless = state.velocities[negative]
    velocities_km_s = pm_dimensionless_velocities_to_km_s(
        negative_dimensionless,
        box_size_mpc=box_size_mpc,
        time_unit_gyr=time_unit_gyr,
    )
    q_cross = relative_velocity_cross_projection_from_velocities_km_s(
        velocities_km_s,
        photon_direction=photon_direction,
    )
    return negative, negative_dimensionless, velocities_km_s, q_cross


def build_payload() -> dict:
    grid_shape = DEFAULT_GRID_SHAPE
    box_size_mpc = DEFAULT_BOX_SIZE_MPC
    time_unit_gyr = DEFAULT_TIME_UNIT_GYR
    photon_direction = DEFAULT_PHOTON_DIRECTION
    state = build_demo_state()
    negative, negative_dimensionless, velocities_km_s, q_cross = negative_qcross_from_state(
        state,
        box_size_mpc=box_size_mpc,
        time_unit_gyr=time_unit_gyr,
        photon_direction=photon_direction,
    )
    speed_km_s = np.linalg.norm(velocities_km_s, axis=1)

    return {
        "description": "Diagnostic Q_cross bridge from a vectorized PM state.",
        "grid_shape": grid_shape,
        "particle_count": int(len(state.positions)),
        "negative_particle_count": int(np.sum(negative)),
        "box_size_mpc": box_size_mpc,
        "time_unit_gyr": time_unit_gyr,
        "velocity_unit_km_s": pm_velocity_unit_km_s(box_size_mpc, time_unit_gyr),
        "photon_direction": photon_direction.tolist(),
        "q_cross_stats": _stats(q_cross),
        "negative_speed_km_s_stats": _stats(speed_km_s),
        "rows": [
            {
                "dimensionless_velocity": negative_dimensionless[i].tolist(),
                "velocity_km_s": velocities_km_s[i].tolist(),
                "q_cross": float(q_cross[i]),
            }
            for i in range(min(4, len(q_cross)))
        ],
        "boundary": (
            "Diagnostic only. This computes Q_cross from PM state velocities after an explicit "
            "time calibration; it is not a survey prediction or an S8 normalization."
        ),
    }


def main() -> None:
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    payload = build_payload()
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")

    q = payload["q_cross_stats"]
    speed = payload["negative_speed_km_s_stats"]
    lines = [
        "# PM State Q_cross Diagnostic",
        "",
        payload["description"],
        "",
        "| metric | value |",
        "|---|---:|",
        f"| grid | {payload['grid_shape']} |",
        f"| particles | {payload['particle_count']} |",
        f"| negative particles | {payload['negative_particle_count']} |",
        f"| velocity unit | {payload['velocity_unit_km_s']:.6g} km/s |",
        f"| Q_cross min | {q['min']:.9g} |",
        f"| Q_cross mean | {q['mean']:.9g} |",
        f"| Q_cross max | {q['max']:.9g} |",
        f"| speed max | {speed['max']:.9g} km/s |",
        "",
        "| dimensionless velocity | velocity km/s | Q_cross |",
        "|---|---|---:|",
    ]
    for row in payload["rows"]:
        lines.append(
            f"| `{row['dimensionless_velocity']}` | `{row['velocity_km_s']}` | "
            f"{row['q_cross']:.9g} |"
        )
    lines.extend(["", payload["boundary"], ""])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {JSON_PATH}")


if __name__ == "__main__":
    main()
