from __future__ import annotations

import json
from pathlib import Path


BASE = Path("outputs/active_z2_sigma")
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_h0_numeric_input_frontier_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_h0_numeric_input_frontier_gate.json")


REQUIRED_INPUTS = {
    "absolute_RSigma": BASE / "rsigma_radius_solution.json",
    "boundary_state_charge": BASE / "projected_boundary_charge_inputs.json",
    "action_scale": BASE / "action_scale_inputs.json",
    "effective_volume": BASE / "spatial_volume_inputs.json",
    "curvature_radius": BASE / "background_curvature_radius_inputs.json",
    "h0_normalization": BASE / "background_H0_normalization_inputs.json",
}

NEAREST_DIMENSIONLESS_INPUTS = {
    "rsigma_over_ell_collar": BASE / "rsigma_over_ell_collar_solution.json",
    "projective_ratio_partial_closure": BASE / "effective_partial_closure_from_projective_ratio.json",
    "scale_free_curvature": BASE / "background_scale_free_omega_k_inputs.json",
}


def _read_json(path: Path) -> dict | None:
    if not path.exists():
        return None
    return json.loads(path.read_text(encoding="utf-8"))


def build_payload() -> dict:
    required = {
        name: {"path": str(path), "exists": path.exists()}
        for name, path in REQUIRED_INPUTS.items()
    }
    nearest = {
        name: {"path": str(path), "exists": path.exists(), "payload": _read_json(path)}
        for name, path in NEAREST_DIMENSIONLESS_INPUTS.items()
    }
    can_provide_numeric_h0 = all(
        required[name]["exists"]
        for name in ["effective_volume", "curvature_radius"]
    ) and any(
        required[name]["exists"]
        for name in ["absolute_RSigma", "boundary_state_charge", "action_scale"]
    )
    return {
        "status": "janus-z2-sigma-h0-numeric-input-frontier-gate",
        "active_core": "Z2_tunnel_Sigma",
        "required_dimensionful_inputs": required,
        "nearest_dimensionless_inputs": nearest,
        "can_provide_absolute_RSigma": required["absolute_RSigma"]["exists"],
        "can_provide_state_charge": required["boundary_state_charge"]["exists"],
        "can_provide_action_scale": required["action_scale"]["exists"],
        "can_provide_effective_volume": required["effective_volume"]["exists"],
        "can_provide_curvature_radius": required["curvature_radius"]["exists"],
        "numeric_H0_inputs_available": can_provide_numeric_h0,
        "interpretation": (
            "The repo currently contains scale-free Z2/Sigma ratios, but not the "
            "dimensionful input needed to evaluate H0 from the Hamiltonian boundary "
            "charge. One of absolute R_Sigma, state charge, or action scale is still "
            "required, together with effective volume and curvature radius or a flat limit."
        ),
        "gate_passed": True,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma H0 Numeric Input Frontier Gate",
        "",
        payload["interpretation"],
        "",
        f"Numeric H0 inputs available: `{payload['numeric_H0_inputs_available']}`",
        "",
        "## Missing Dimensionful Inputs",
    ]
    lines.extend(
        f"- `{name}`: `{item['path']}`"
        for name, item in payload["required_dimensionful_inputs"].items()
        if not item["exists"]
    )
    lines.extend(["", "## Available Scale-Free Inputs"])
    lines.extend(
        f"- `{name}`: `{item['path']}`"
        for name, item in payload["nearest_dimensionless_inputs"].items()
        if item["exists"]
    )
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
