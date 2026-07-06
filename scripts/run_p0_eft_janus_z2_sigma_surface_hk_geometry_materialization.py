from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z2_sigma_cartan_ghy_rsigma_certificate_to_isotropic_radius_collar_gate import (
    build_payload as build_certificate_to_collar,
)
from scripts.build_p0_eft_janus_z2_sigma_cartan_ghy_rsigma_isotropic_radius_collar_input_writer_gate import (
    build_payload as build_isotropic_collar,
)
from scripts.build_p0_eft_janus_z2_sigma_cartan_ghy_rsigma_gaussian_collar_input_writer_gate import (
    build_payload as build_gaussian_collar,
)
from scripts.build_p0_eft_janus_z2_sigma_cartan_ghy_rsigma_local_chart_input_writer_gate import (
    build_payload as build_local_chart,
)
from scripts.build_p0_eft_janus_z2_sigma_cartan_ghy_rsigma_chart_stencil_input_writer_gate import (
    build_payload as build_chart_stencil,
)
from scripts.build_p0_eft_janus_z2_sigma_cartan_ghy_rsigma_embedding_stencil_input_writer_gate import (
    build_payload as build_embedding_stencil,
)
from scripts.derive_p0_eft_janus_z2_sigma_surface_hk_radial_geometry_input_writer_gate import (
    build_payload as build_surface_geometry,
)


REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_surface_hk_geometry_materialization.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_surface_hk_geometry_materialization.json"
)


def build_payload() -> dict:
    steps = [
        ("certificate_to_isotropic_radius_collar", build_certificate_to_collar),
        ("isotropic_radius_collar", build_isotropic_collar),
        ("gaussian_collar", build_gaussian_collar),
        ("local_chart", build_local_chart),
        ("chart_stencil", build_chart_stencil),
        ("embedding_stencil", build_embedding_stencil),
        ("surface_hk_radial_geometry", build_surface_geometry),
    ]
    results = []
    for name, builder in steps:
        result = builder()
        results.append(
            {
                "step": name,
                "gate_passed": bool(result.get("gate_passed")),
                "primary_blocker": result.get("primary_blocker"),
                "validation_error": result.get("validation_error"),
            }
        )
        if not result.get("gate_passed"):
            break
    ready = bool(results and results[-1]["step"] == "surface_hk_radial_geometry" and results[-1]["gate_passed"])
    return {
        "status": "janus-z2-sigma-surface-hk-geometry-materialization",
        "active_core": "Z2_tunnel_Sigma",
        "steps": results,
        "surface_hk_geometry_materialized": ready,
        "gate_passed": ready,
        "primary_blocker": "none" if ready else results[-1]["primary_blocker"],
        "next_required": []
        if ready
        else [
            "close_first_failed_step_in_geometry_materialization_chain",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Surface h/K Geometry Materialization",
        "",
        f"Gate passed: `{payload['gate_passed']}`",
        f"Primary blocker: `{payload['primary_blocker']}`",
        "",
        "## Steps",
    ]
    for step in payload["steps"]:
        lines.append(
            f"- `{step['step']}` passed=`{step['gate_passed']}` blocker=`{step['primary_blocker']}`"
        )
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
