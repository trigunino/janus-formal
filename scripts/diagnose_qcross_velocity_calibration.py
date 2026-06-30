from __future__ import annotations

from pathlib import Path
import json

import numpy as np

from janus_lab.lensing import relative_velocity_cross_projection_from_velocities_km_s
from janus_lab.physical_units import pm_dimensionless_velocities_to_km_s, pm_velocity_unit_km_s


REPORT_PATH = Path("outputs/reports/qcross_velocity_calibration.md")
JSON_PATH = Path("outputs/reports/qcross_velocity_calibration.json")


def main() -> None:
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    box_size_mpc = 1000.0
    time_unit_gyr = 1.0
    photon_direction = np.asarray([1.0, 0.0, 0.0])
    dimensionless_velocities = np.asarray(
        [
            [0.0, 0.0, 0.0],
            [1.0e-4, 0.0, 0.0],
            [-1.0e-4, 0.0, 0.0],
            [0.0, 1.0e-4, 0.0],
        ]
    )
    velocities_km_s = pm_dimensionless_velocities_to_km_s(
        dimensionless_velocities,
        box_size_mpc=box_size_mpc,
        time_unit_gyr=time_unit_gyr,
    )
    q_cross = relative_velocity_cross_projection_from_velocities_km_s(
        velocities_km_s,
        photon_direction=photon_direction,
    )
    payload = {
        "description": "Diagnostic bridge from dimensionless PM velocities to Q_cross.",
        "box_size_mpc": box_size_mpc,
        "time_unit_gyr": time_unit_gyr,
        "velocity_unit_km_s": pm_velocity_unit_km_s(box_size_mpc, time_unit_gyr),
        "photon_direction": photon_direction.tolist(),
        "rows": [
            {
                "dimensionless_velocity": dimensionless_velocities[i].tolist(),
                "velocity_km_s": velocities_km_s[i].tolist(),
                "q_cross": float(q_cross[i]),
            }
            for i in range(len(q_cross))
        ],
        "boundary": (
            "Calibration diagnostic only. The time unit is explicit; do not apply to PM outputs "
            "without a physical time calibration."
        ),
    }
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Q_cross Velocity Calibration",
        "",
        payload["description"],
        "",
        f"Velocity unit: `{payload['velocity_unit_km_s']:.6g} km/s`.",
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
