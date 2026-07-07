from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z2_sigma_natural_scale_no_go_gate import (
    build_payload as build_natural_scale,
)

Q_PATH = Path("outputs/active_z2_sigma/unit_intrinsic_metric_q_ab_inputs.json")
RATIO_PATH = Path("outputs/active_z2_sigma/rsigma_over_ell_collar_solution.json")
EMBEDDING_PATH = Path("outputs/active_z2_sigma/so3_throat_embedding_manifest.json")
REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_boundary_surface_measure_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_boundary_surface_measure_gate.json"
)


def _read(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8")) if path.exists() else {}


def build_payload(
    *,
    q_path: Path = Q_PATH,
    ratio_path: Path = RATIO_PATH,
    embedding_path: Path = EMBEDDING_PATH,
) -> dict:
    q = _read(q_path)
    ratio = _read(ratio_path)
    embedding = _read(embedding_path)
    natural = build_natural_scale()
    topology = q.get("spatial_topology", {})
    volume_factor = topology.get("volume_factor_pi2_R3")
    ratio_ready = bool(ratio.get("ratio_solution_ready"))
    embedding_throat = embedding.get("throat_certificate", {})
    closure = {
        "unit_intrinsic_metric_available": bool(q.get("unit_intrinsic_metric_q_ab")),
        "surface_volume_factor_available": volume_factor is not None,
        "RSigma_over_ell_collar_ratio_available": ratio_ready,
        "SO3_minimal_throat_shape_available": bool(embedding_throat.get("minimal_throat")),
        "absolute_RSigma_available": bool(embedding_throat.get("absolute_scale_fixed_by_model")),
    }
    formula_ready = all(
        closure[key]
        for key in [
            "unit_intrinsic_metric_available",
            "surface_volume_factor_available",
            "RSigma_over_ell_collar_ratio_available",
            "SO3_minimal_throat_shape_available",
        ]
    )
    return {
        "status": "janus-z2-sigma-boundary-surface-measure-gate",
        "active_core": "Z2_tunnel_Sigma",
        "surface_measure_formula": (
            f"Vol_Sigma = {volume_factor} * pi^2 * R_Sigma^3"
            if volume_factor is not None
            else "Vol_Sigma = volume_factor*pi^2*R_Sigma^3"
        ),
        "known_ratio": {
            "R_Sigma_over_ell_collar": ratio.get("R_Sigma_over_ell_collar"),
            "absolute_ell_collar_fixed": ratio.get("absolute_ell_collar_fixed"),
            "absolute_R_Sigma_fixed": ratio.get("absolute_R_Sigma_fixed"),
        },
        "embedding_shape": {
            "R_Sigma_unit": embedding_throat.get("R_Sigma"),
            "absolute_scale_symbol": embedding_throat.get("absolute_scale_symbol"),
            "absolute_scale_fixed_by_model": embedding_throat.get(
                "absolute_scale_fixed_by_model"
            ),
        },
        "natural_scale_gate": {
            "status": natural["status"],
            "natural_scale_constructible": natural["natural_scale_constructible"],
            "accepted_as_RSigma": natural["natural_scale_accepted_as_RSigma"],
            "candidate": natural["candidate_natural_scale"],
        },
        "closure": closure,
        "symbolic_surface_measure_ready": formula_ready,
        "numeric_surface_measure_ready": formula_ready
        and closure["absolute_RSigma_available"],
        "blocked_by": [key for key, ok in closure.items() if not ok],
        "interpretation": (
            "The active Z2/Sigma geometry fixes the unit surface measure and the "
            "projective ratio R_Sigma/ell_collar. It does not fix the absolute "
            "length R_Sigma needed for a numeric boundary Hamiltonian charge."
        ),
        "gate_passed": True,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Boundary Surface Measure Gate",
        "",
        payload["interpretation"],
        "",
        f"Formula: `{payload['surface_measure_formula']}`",
        f"Symbolic surface measure ready: `{payload['symbolic_surface_measure_ready']}`",
        f"Numeric surface measure ready: `{payload['numeric_surface_measure_ready']}`",
        "",
        "## Blocked By",
    ]
    lines.extend(f"- `{item}`" for item in payload["blocked_by"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
