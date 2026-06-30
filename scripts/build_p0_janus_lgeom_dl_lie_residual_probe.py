from __future__ import annotations

from pathlib import Path
import json

import numpy as np

from janus_lab.weakfield_geometry import (
    derivative_tetrad_map_1p1,
    diagonal_tetrad_1p1,
    diagonal_tetrad_map_1p1,
    max_lie_algebra_residual_1p1,
    max_lorentz_residual_1p1,
    weakfield_metric_1p1,
)


REPORT_PATH = Path("outputs/reports/p0_janus_lgeom_dl_lie_residual_probe.md")
JSON_PATH = Path("outputs/reports/p0_janus_lgeom_dl_lie_residual_probe.json")


def build_payload() -> dict:
    n = 64
    box = 2.0 * np.pi
    x = np.arange(n) * box / n
    phi = 1e-3 * np.cos(x)
    plus_tetrad = diagonal_tetrad_1p1(weakfield_metric_1p1(phi))
    equal_map = diagonal_tetrad_map_1p1(plus_tetrad, plus_tetrad)
    mismatch_map = diagonal_tetrad_map_1p1(
        plus_tetrad,
        diagonal_tetrad_1p1(weakfield_metric_1p1(-phi)),
    )
    equal_lie = max_lie_algebra_residual_1p1(equal_map, derivative_tetrad_map_1p1(equal_map, box))
    mismatch_lie = max_lie_algebra_residual_1p1(
        mismatch_map,
        derivative_tetrad_map_1p1(mismatch_map, box),
    )
    metrics = {
        "equal_branch_lorentz_residual": max_lorentz_residual_1p1(equal_map),
        "equal_branch_lie_residual": equal_lie,
        "mismatched_branch_lorentz_residual": max_lorentz_residual_1p1(mismatch_map),
        "mismatched_branch_lie_residual": mismatch_lie,
    }
    return {
        "description": "Diagnostic D L Lie-algebra residual for raw weak-field L_geom.",
        "status": "lgeom-dl-lie-residual-probe-diagnostic",
        "depends_on": [
            "p0_janus_lgeom_tetrad_map_residual_probe",
            "p0_janus_same_l_transport_stack_gate",
        ],
        "metrics": metrics,
        "equal_branch_passes_lie_algebra": equal_lie < 1e-12,
        "mismatched_branch_fails_lie_algebra": mismatch_lie > 0.0,
        "dl_source_derived": False,
        "raw_lgeom_promoted": False,
        "diagnostic_only": True,
        "uses_observational_fit": False,
        "physics_closed": False,
        "prediction_ready": False,
        "boundary": (
            "This computes L^{-1}D L for raw L_geom and checks the Lorentz Lie algebra. "
            "It rejects promotion of raw L_geom; it does not derive a Janus D L law."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Janus Lgeom DL Lie Residual Probe",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Equal branch passes Lie algebra: {payload['equal_branch_passes_lie_algebra']}",
        f"Mismatched branch fails Lie algebra: {payload['mismatched_branch_fails_lie_algebra']}",
        f"D L source-derived: {payload['dl_source_derived']}",
        f"Raw Lgeom promoted: {payload['raw_lgeom_promoted']}",
        f"Diagnostic only: {payload['diagnostic_only']}",
        f"Uses observational fit: {payload['uses_observational_fit']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Metrics",
        "",
        "| metric | value |",
        "|---|---:|",
    ]
    for name, value in payload["metrics"].items():
        lines.append(f"| {name} | {value:.6g} |")
    lines.extend(["", f"Boundary: {payload['boundary']}", ""])
    return "\n".join(lines)


def write_reports(report_path: Path = REPORT_PATH, json_path: Path = JSON_PATH) -> dict:
    report_path.parent.mkdir(parents=True, exist_ok=True)
    json_path.parent.mkdir(parents=True, exist_ok=True)
    payload = build_payload()
    json_path.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    report_path.write_text(render_markdown(payload), encoding="utf-8")
    return payload


def main() -> None:
    write_reports()
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {JSON_PATH}")


if __name__ == "__main__":
    main()
