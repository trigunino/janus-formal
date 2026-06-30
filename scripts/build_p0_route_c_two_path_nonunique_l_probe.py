from __future__ import annotations

from pathlib import Path
import json
import sys

import numpy as np
from scipy import linalg


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_route_c_small_loop_holonomy_numeric_probe import (
    ETA,
    boost_generator,
    eta_lie_error,
)


REPORT_PATH = Path("outputs/reports/p0_route_c_two_path_nonunique_l_probe.md")
JSON_PATH = Path("outputs/reports/p0_route_c_two_path_nonunique_l_probe.json")
TOLERANCE = 1e-10


def build_payload() -> dict:
    area_x = 0.18
    area_y = 0.14
    generator_x = boost_generator("x")
    generator_y = boost_generator("y")
    path_xy = linalg.expm(area_y * generator_y) @ linalg.expm(area_x * generator_x)
    path_yx = linalg.expm(area_x * generator_x) @ linalg.expm(area_y * generator_y)
    commutator = generator_x @ generator_y - generator_y @ generator_x
    same_endpoint_residual = float(linalg.norm(path_xy - path_yx))
    commutator_norm = float(linalg.norm(commutator))
    return {
        "description": (
            "Route C negative probe: two admissible noncommuting holonomy paths "
            "produce different L transports. Without a Janus path rule, the same "
            "local curvature data underselects L."
        ),
        "status": "two-path-nonunique-l-probe-open",
        "tooling": ["numpy", "scipy.linalg.expm"],
        "path_families": ["x_then_y", "y_then_x"],
        "area_x": area_x,
        "area_y": area_y,
        "generator_x_lorentz_algebra": eta_lie_error(generator_x) < TOLERANCE,
        "generator_y_lorentz_algebra": eta_lie_error(generator_y) < TOLERANCE,
        "path_xy_metric_error": float(np.max(np.abs(path_xy.T @ ETA @ path_xy - ETA))),
        "path_yx_metric_error": float(np.max(np.abs(path_yx.T @ ETA @ path_yx - ETA))),
        "commutator_norm": commutator_norm,
        "two_path_l_residual": same_endpoint_residual,
        "two_paths_both_admissible_locally": True,
        "two_paths_select_different_l": same_endpoint_residual > TOLERANCE,
        "path_rule_required_for_unique_l": True,
        "janus_path_rule_supplied": False,
        "uses_observational_fit": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "The negative control fires: locally admissible Lorentz transports along "
            "two noncommuting path orderings give different L. Therefore curvature "
            "plus Lorentz admissibility is not enough; Janus must supply the path rule."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Route C Two-Path Nonunique L Probe",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Path families: {payload['path_families']}",
        f"Generator x Lorentz algebra: {payload['generator_x_lorentz_algebra']}",
        f"Generator y Lorentz algebra: {payload['generator_y_lorentz_algebra']}",
        f"Commutator norm: {payload['commutator_norm']:.12g}",
        f"Two-path L residual: {payload['two_path_l_residual']:.12g}",
        f"Two paths select different L: {payload['two_paths_select_different_l']}",
        f"Path rule required for unique L: {payload['path_rule_required_for_unique_l']}",
        f"Janus path rule supplied: {payload['janus_path_rule_supplied']}",
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
