from __future__ import annotations

from pathlib import Path
import json

import numpy as np

from janus_lab.particle_mesh_3d_vectorized import deposit_cloud_in_cell_3d_vectorized

try:
    from scripts.diagnose_pm_state_qcross import (
        DEFAULT_BOX_SIZE,
        DEFAULT_BOX_SIZE_MPC,
        DEFAULT_GRID_SHAPE,
        DEFAULT_PHOTON_DIRECTION,
        DEFAULT_TIME_UNIT_GYR,
        _stats,
        build_demo_state,
        negative_qcross_from_state,
    )
except ModuleNotFoundError:
    from diagnose_pm_state_qcross import (
        DEFAULT_BOX_SIZE,
        DEFAULT_BOX_SIZE_MPC,
        DEFAULT_GRID_SHAPE,
        DEFAULT_PHOTON_DIRECTION,
        DEFAULT_TIME_UNIT_GYR,
        _stats,
        build_demo_state,
        negative_qcross_from_state,
    )


REPORT_PATH = Path("outputs/reports/pm_qcross_lensing_source.md")
JSON_PATH = Path("outputs/reports/pm_qcross_lensing_source.json")


def build_payload() -> dict:
    state = build_demo_state()
    negative, _, _, q_cross = negative_qcross_from_state(
        state,
        box_size_mpc=DEFAULT_BOX_SIZE_MPC,
        time_unit_gyr=DEFAULT_TIME_UNIT_GYR,
        photon_direction=DEFAULT_PHOTON_DIRECTION,
    )

    positive_density, negative_density = deposit_cloud_in_cell_3d_vectorized(
        state,
        grid_shape=DEFAULT_GRID_SHAPE,
        box_size=DEFAULT_BOX_SIZE,
    )
    weighted_state = state.copy()
    weighted_state.mass_abs[negative] *= q_cross
    _, negative_qcross_density = deposit_cloud_in_cell_3d_vectorized(
        weighted_state,
        grid_shape=DEFAULT_GRID_SHAPE,
        box_size=DEFAULT_BOX_SIZE,
    )

    equal_projection_source = positive_density - negative_density
    qcross_source = positive_density - negative_qcross_density
    centered_qcross_source = qcross_source - float(np.mean(qcross_source))
    source_delta = centered_qcross_source - (
        equal_projection_source - float(np.mean(equal_projection_source))
    )

    return {
        "description": "Diagnostic PM source grid with negative density weighted by Q_cross.",
        "grid_shape": DEFAULT_GRID_SHAPE,
        "q_cross_stats": _stats(q_cross),
        "centered_qcross_source_stats": _stats(centered_qcross_source),
        "source_delta_stats": _stats(source_delta),
        "boundary": (
            "Diagnostic only. The grid source is rho_plus - Q_cross rho_minus from "
            "calibrated PM velocities; it is not a final tensor lensing source."
        ),
    }


def main() -> None:
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    payload = build_payload()
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")

    q = payload["q_cross_stats"]
    source = payload["centered_qcross_source_stats"]
    delta = payload["source_delta_stats"]
    lines = [
        "# PM Q_cross Lensing Source",
        "",
        payload["description"],
        "",
        "| metric | value |",
        "|---|---:|",
        f"| grid | {payload['grid_shape']} |",
        f"| Q_cross min | {q['min']:.9g} |",
        f"| Q_cross mean | {q['mean']:.9g} |",
        f"| Q_cross max | {q['max']:.9g} |",
        f"| centered source min | {source['min']:.9g} |",
        f"| centered source max | {source['max']:.9g} |",
        f"| source delta std | {delta['std']:.9g} |",
        "",
        payload["boundary"],
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {JSON_PATH}")


if __name__ == "__main__":
    main()
