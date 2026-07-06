from __future__ import annotations

import json
from pathlib import Path


COEFFICIENT_PATH = Path("outputs/active_z2_sigma/surface_hk_active_density_coefficients.json")
TRACE_TARGET_PATH = Path("outputs/active_z2_sigma/counterterm_trace_residual_inputs.json")
REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_surface_hk_active_density_coefficient_route_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_surface_hk_active_density_coefficient_route_gate.json"
)


def _active_exists(path: Path) -> bool:
    if not path.exists():
        return False
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
        return payload.get("active_core") == "Z2_tunnel_Sigma" and payload.get("source") == "active_derived"
    except Exception:
        return False


def build_payload(
    *,
    coefficient_path: Path = COEFFICIENT_PATH,
    trace_target_path: Path = TRACE_TARGET_PATH,
) -> dict:
    coefficient_ready = _active_exists(coefficient_path)
    trace_target_ready = _active_exists(trace_target_path)
    routes = {
        "direct_active_density": {
            "ready": coefficient_ready,
            "path": str(coefficient_path),
            "meaning": "a0..a3 already derived from active Janus/Sigma action",
        },
        "residual_matching": {
            "ready": trace_target_ready,
            "path": str(trace_target_path),
            "meaning": "solve a_i from active R_h/R_K trace targets, not observations",
        },
        "symmetry_no_go": {
            "ready": False,
            "meaning": "prove polynomial basis insufficient and replace by non-polynomial active density",
        },
    }
    selected = (
        "direct_active_density"
        if coefficient_ready
        else "residual_matching"
        if trace_target_ready
        else "none"
    )
    return {
        "status": "janus-z2-sigma-surface-hk-active-density-coefficient-route-gate",
        "active_core": "Z2_tunnel_Sigma",
        "routes": routes,
        "selected_route": selected,
        "coefficient_route_ready": coefficient_ready or trace_target_ready,
        "gate_passed": coefficient_ready or trace_target_ready,
        "primary_blocker": "none"
        if coefficient_ready or trace_target_ready
        else "active_density_coefficients_or_active_residual_trace_targets",
        "forbidden": [
            "free_a0_a1_a2_a3",
            "observational_fit_for_a_i",
            "reuse_Cartan_GHY_linear_K_as_non_GHY_density",
            "legacy_Z4_coefficient_import",
        ],
        "next_required": []
        if coefficient_ready or trace_target_ready
        else [
            "derive_surface_hk_active_density_coefficients_json",
            "or_derive_counterterm_trace_residual_inputs_json_from_active_boundary_variation",
            "or_prove_polynomial_basis_no_go_and_replace_density",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Surface h/K Active Density Coefficient Route Gate",
        "",
        f"Gate passed: `{payload['gate_passed']}`",
        f"Selected route: `{payload['selected_route']}`",
        f"Primary blocker: `{payload['primary_blocker']}`",
        "",
        "## Routes",
    ]
    for name, route in payload["routes"].items():
        lines.append(f"- `{name}` ready=`{route['ready']}`")
    lines.extend(["", "## Forbidden"])
    lines.extend(f"- `{item}`" for item in payload["forbidden"])
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
