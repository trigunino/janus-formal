from __future__ import annotations

import json
from pathlib import Path


STENCIL_TENSOR_PATH = Path("outputs/active_z2_sigma/cartan_ghy_rsigma_radial_primitives_inputs.json")
NORMAL_FLOW_INPUT_PATH = Path("outputs/active_z2_sigma/surface_hk_normal_flow_geometry_inputs.json")
RICCATI_OUTPUT_PATH = Path("outputs/active_z2_sigma/surface_hk_radial_tensor_geometry_inputs.json")
SURFACE_TENSOR_PATH = Path("outputs/active_z2_sigma/surface_hk_radial_tensor_geometry_inputs.json")
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_surface_hk_geometry_dual_route_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_surface_hk_geometry_dual_route_gate.json")


def _active_exists(path: Path) -> bool:
    if not path.exists():
        return False
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
        return payload.get("active_core") == "Z2_tunnel_Sigma" and payload.get("source") == "active_derived"
    except Exception:
        return False


def build_payload() -> dict:
    stencil_ready = _active_exists(STENCIL_TENSOR_PATH)
    normal_flow_ready = _active_exists(NORMAL_FLOW_INPUT_PATH)
    surface_tensor_ready = _active_exists(SURFACE_TENSOR_PATH)
    route_ready = surface_tensor_ready or stencil_ready or normal_flow_ready
    selected_route = (
        "surface_hk_radial_tensor_geometry_inputs"
        if surface_tensor_ready
        else "cartan_ghy_embedding_stencil_tensor_primitives"
        if stencil_ready
        else "normal_flow_K_ab_R_nabn"
        if normal_flow_ready
        else "none"
    )
    return {
        "status": "janus-z2-sigma-surface-hk-geometry-dual-route-gate",
        "active_core": "Z2_tunnel_Sigma",
        "routes": {
            "surface_tensor_direct": {
                "path": str(SURFACE_TENSOR_PATH),
                "ready": surface_tensor_ready,
            },
            "stencil_route": {
                "path": str(STENCIL_TENSOR_PATH),
                "ready": stencil_ready,
                "bridge": "feed directly to surface_hk_radial_geometry_input_writer_gate",
            },
            "normal_flow_route": {
                "path": str(NORMAL_FLOW_INPUT_PATH),
                "ready": normal_flow_ready,
                "requires": ["K_ab", "R_nabn"],
                "output": str(RICCATI_OUTPUT_PATH),
            },
        },
        "selected_route": selected_route,
        "geometry_route_ready": route_ready,
        "gate_passed": route_ready,
        "primary_blocker": "none"
        if route_ready
        else "active_surface_tensor_or_stencil_or_normal_flow_geometry",
        "next_required": []
        if route_ready
        else [
            "derive_cartan_ghy_rsigma_radial_primitives_inputs_from_active_stencil",
            "or_derive_surface_hk_normal_flow_geometry_inputs_from_K_ab_R_nabn",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Surface h/K Geometry Dual Route Gate",
        "",
        f"Gate passed: `{payload['gate_passed']}`",
        f"Selected route: `{payload['selected_route']}`",
        f"Primary blocker: `{payload['primary_blocker']}`",
        "",
        "## Routes",
    ]
    for name, route in payload["routes"].items():
        lines.append(f"- `{name}` ready=`{route['ready']}` path=`{route['path']}`")
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
