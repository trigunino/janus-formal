from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_surface_hk_normal_flow_geometry_formula_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_surface_hk_normal_flow_geometry_formula_gate.json"
)


def build_payload() -> dict:
    formulas = {
        "proper_normal_gauge": "R is proper signed distance along the Z2/Sigma normal",
        "partial_R_h_ab": "2*K_ab",
        "partial_R_K_ab": "R_nabn + K_a^c*K_cb",
        "R_nabn": "R_{mu nu rho sigma} n^mu e_a^nu n^rho e_b^sigma",
    }
    requirements = {
        "active_K_ab_available": False,
        "active_R_nabn_available": False,
        "proper_normal_gauge_fixed": True,
        "K_ab_convention_compatible": True,
    }
    return {
        "status": "janus-z2-sigma-surface-hk-normal-flow-geometry-formula-gate",
        "active_core": "Z2_tunnel_Sigma",
        "source": "embedding_normal_flow_geometry",
        "formulas": formulas,
        "requirements": requirements,
        "normal_flow_formula_ready": True,
        "surface_hk_radial_tensor_geometry_derivable_from_normal_flow": all(
            requirements.values()
        ),
        "gate_passed": all(requirements.values()),
        "primary_blocker": "none"
        if all(requirements.values())
        else "active_K_ab_and_R_nabn_projection",
        "next_required": [
            "derive_active_K_ab_on_Sigma",
            "derive_active_R_nabn_on_Sigma",
            "write_surface_hk_radial_tensor_geometry_inputs_json",
        ],
        "fallback_route": "embedding_radial_stencil_if_R_nabn_not_available",
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# Janus Z2/Sigma Surface h/K Normal Flow Geometry Formula Gate",
        "",
        f"Gate passed: `{payload['gate_passed']}`",
        f"Primary blocker: `{payload['primary_blocker']}`",
        "",
        "## Formulas",
    ]
    lines.extend(f"- `{key}`: `{value}`" for key, value in payload["formulas"].items())
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    return "\n".join(lines)


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(render_markdown(payload), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
