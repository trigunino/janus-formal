from __future__ import annotations

from pathlib import Path
import json

import numpy as np

from janus_lab.weakfield_geometry import (
    diagonal_tetrad_1p1,
    diagonal_tetrad_map_1p1,
    max_lorentz_residual_1p1,
    weakfield_metric_1p1,
)


REPORT_PATH = Path("outputs/reports/p0_janus_lgeom_tetrad_map_residual_probe.md")
JSON_PATH = Path("outputs/reports/p0_janus_lgeom_tetrad_map_residual_probe.json")


def build_payload() -> dict:
    x = np.linspace(0.0, 2.0 * np.pi, 32, endpoint=False)
    phi_plus = 1e-3 * np.cos(x)
    phi_minus_equal = phi_plus.copy()
    phi_minus_opposite = -phi_plus
    tetrad_plus = diagonal_tetrad_1p1(weakfield_metric_1p1(phi_plus))
    tetrad_equal = diagonal_tetrad_1p1(weakfield_metric_1p1(phi_minus_equal))
    tetrad_opposite = diagonal_tetrad_1p1(weakfield_metric_1p1(phi_minus_opposite))
    equal_residual = max_lorentz_residual_1p1(diagonal_tetrad_map_1p1(tetrad_plus, tetrad_equal))
    opposite_residual = max_lorentz_residual_1p1(diagonal_tetrad_map_1p1(tetrad_plus, tetrad_opposite))
    metrics = {
        "equal_branch_lorentz_residual": equal_residual,
        "opposite_branch_lorentz_residual": opposite_residual,
        "max_abs_phi_plus": float(np.max(np.abs(phi_plus))),
    }
    return {
        "description": "Diagnostic residual for raw L_geom=e_plus^{-1}e_minus from weak-field tetrads.",
        "status": "lgeom-tetrad-map-residual-probe-diagnostic",
        "depends_on": [
            "p0_janus_same_l_transport_stack_gate",
            "p0_janus_weakfield_lgeom_lorentz_no_go_gate",
        ],
        "metrics": metrics,
        "equal_branch_passes_lorentz": equal_residual < 1e-12,
        "mismatched_branch_fails_lorentz": opposite_residual > 0.0,
        "raw_lgeom_promoted": False,
        "diagnostic_only": True,
        "uses_observational_fit": False,
        "physics_closed": False,
        "prediction_ready": False,
        "boundary": (
            "This confirms the local weak-field no-go shape: raw L_geom is Lorentz only "
            "on the equal-tetrad branch. It does not derive the accepted same-L transport."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Janus Lgeom Tetrad Map Residual Probe",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Equal branch passes Lorentz: {payload['equal_branch_passes_lorentz']}",
        f"Mismatched branch fails Lorentz: {payload['mismatched_branch_fails_lorentz']}",
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
