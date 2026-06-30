from __future__ import annotations

from pathlib import Path
import json
import sys

import numpy as np
from scipy import linalg


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_weakfield_tetrad_pipeline_probe import (
    ETA,
    build_toy_weakfield_fields,
    curvature_injection_rows,
)


REPORT_PATH = Path("outputs/reports/p0_route_c_small_loop_holonomy_numeric_probe.md")
JSON_PATH = Path("outputs/reports/p0_route_c_small_loop_holonomy_numeric_probe.json")
TOLERANCE = 1e-10


def boost_generator(axis: str) -> np.ndarray:
    index = {"x": 1, "y": 2, "z": 3}[axis]
    generator = np.zeros((4, 4), dtype=float)
    generator[0, index] = 1.0
    generator[index, 0] = 1.0
    return generator


def eta_lie_error(matrix: np.ndarray) -> float:
    return float(np.max(np.abs(matrix.T @ ETA + ETA @ matrix)))


def build_payload() -> dict:
    _, delta_phi, delta_psi = build_toy_weakfield_fields()
    curvature_rows, curvature_residual = curvature_injection_rows(delta_phi, delta_psi)
    curvature_by_name = {row["row"]: row["value"] for row in curvature_rows}
    coefficient = float(curvature_by_name["Delta_F_0x0x"])
    area = 0.25
    curvature_matrix = coefficient * boost_generator("x")
    holonomy = linalg.expm(area * curvature_matrix)
    first_order = np.eye(4) + area * curvature_matrix
    segmented = linalg.expm(0.5 * area * curvature_matrix) @ linalg.expm(0.5 * area * curvature_matrix)

    noncommuting_curvature = (
        coefficient * boost_generator("x")
        + float(curvature_by_name["Delta_F_0y0y"]) * boost_generator("y")
    )
    ordered_xy = linalg.expm(0.5 * area * coefficient * boost_generator("x")) @ linalg.expm(
        0.5 * area * float(curvature_by_name["Delta_F_0y0y"]) * boost_generator("y")
    )
    combined_xy = linalg.expm(0.5 * area * noncommuting_curvature)
    defected_candidate = curvature_matrix + 0.01 * np.eye(4)

    first_order_residual = float(linalg.norm(holonomy - first_order))
    segmentation_residual = float(linalg.norm(holonomy - segmented))
    path_order_residual = float(linalg.norm(ordered_xy - combined_xy))
    defected_lie_error = eta_lie_error(defected_candidate)

    return {
        "description": (
            "Route C numeric probe for the weak-field Phi_R candidate: construct a "
            "Lorentz-algebra curvature matrix from Delta_R rows and test small-loop "
            "holonomy, segmentation, path-order sensitivity, and defect rejection."
        ),
        "status": "small-loop-holonomy-numeric-probe-open",
        "depends_on": [
            "p0_weakfield_tetrad_pipeline_probe",
            "p0_route_c_phi_r_relative_curvature_selector_probe",
        ],
        "tooling": ["numpy", "scipy.linalg.expm"],
        "curvature_source": "Delta_F_0x0x from weak-field relative curvature rows",
        "loop_area": area,
        "curvature_coefficient": coefficient,
        "connection_to_curvature_max_residual": curvature_residual,
        "eta_lie_error": eta_lie_error(curvature_matrix),
        "defected_eta_lie_error": defected_lie_error,
        "first_order_holonomy_residual": first_order_residual,
        "constant_curvature_segmentation_residual": segmentation_residual,
        "noncommuting_path_order_residual": path_order_residual,
        "weakfield_relative_curvature_rows_used": True,
        "constant_curvature_holonomy_first_order_closes": first_order_residual < 1e-4,
        "constant_curvature_segmentation_closes": segmentation_residual < TOLERANCE,
        "noncommuting_path_order_changes_holonomy": path_order_residual > TOLERANCE,
        "lorentz_algebra_candidate": eta_lie_error(curvature_matrix) < TOLERANCE,
        "curl_defected_phi_r_rejected": defected_lie_error > TOLERANCE,
        "phi_r_free_insert_allowed": False,
        "path_rule_source_derived": False,
        "l_uniquely_selected": False,
        "uses_observational_fit": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "The weak-field Phi_R candidate passes the bounded Lorentz-algebra and "
            "constant-curvature small-loop checks. It still does not select a unique "
            "L because noncommuting curvature is path-order sensitive and Janus has "
            "not supplied the source path rule."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Route C Small-Loop Holonomy Numeric Probe",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Curvature source: {payload['curvature_source']}",
        f"Loop area: {payload['loop_area']}",
        f"Curvature coefficient: {payload['curvature_coefficient']:.12g}",
        f"Eta Lie error: {payload['eta_lie_error']:.3g}",
        f"Defected eta Lie error: {payload['defected_eta_lie_error']:.3g}",
        f"First-order holonomy residual: {payload['first_order_holonomy_residual']:.12g}",
        f"Segmentation residual: {payload['constant_curvature_segmentation_residual']:.3g}",
        f"Path-order residual: {payload['noncommuting_path_order_residual']:.12g}",
        f"Lorentz-algebra candidate: {payload['lorentz_algebra_candidate']}",
        f"Curl-defected Phi_R rejected: {payload['curl_defected_phi_r_rejected']}",
        f"Phi_R free insert allowed: {payload['phi_r_free_insert_allowed']}",
        f"Path rule source derived: {payload['path_rule_source_derived']}",
        f"L uniquely selected: {payload['l_uniquely_selected']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        f"Verdict: {payload['verdict']}",
        "",
    ]
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
