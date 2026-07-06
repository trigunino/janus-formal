from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_rcurv_gauss_codazzi_projection_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_rcurv_gauss_codazzi_projection_gate.json"
)


def build_payload() -> dict:
    closure = {
        "intrinsic_spatial_slice_sign_declared": True,
        "gauss_codazzi_identity_declared": True,
        "projective_volume_surface_ratio_declared": True,
        "dimensionless_Rcurv_relation_available": True,
        "dimensionful_scale_from_boundary_hamiltonian_available": False,
        "R_curv_Z2Sigma_m_numeric_ready": False,
    }
    return {
        "status": "janus-z2-sigma-rcurv-gauss-codazzi-projection-gate",
        "active_core": "Z2_tunnel_Sigma",
        "source": "Gauss_Codazzi_volume_surface_projection",
        "projection_formula": (
            "R3_Z2Sigma = 6*k_Z2Sigma/R_curv_Z2Sigma^2, with the "
            "dimensionful R_curv scale fixed only after the same boundary "
            "Hamiltonian/time normalization that fixes H0."
        ),
        "closure": closure,
        "ready_for_background_curvature_input": all(closure.values()),
        "forbidden_shortcuts": [
            "do_not_set_R_curv_from_observed_H0",
            "do_not_import_LambdaCDM_curvature_prior",
            "do_not_treat_dimensionless_projective_ratio_as_meter_scale",
        ],
        "next_required": [
            "derive_dimensionful_scale_from_boundary_hamiltonian_projection",
            "combine_with_k_Z2Sigma_and_R3_Z2Sigma_Gauss_Codazzi_identity",
            "write_background_curvature_branch_inputs_json",
        ],
        "gate_passed": True,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma R_curv Gauss-Codazzi Projection Gate",
        "",
        payload["projection_formula"],
        "",
        f"Ready for curvature input: `{payload['ready_for_background_curvature_input']}`",
        "",
        "## Closure",
    ]
    lines.extend(f"- `{key}`: `{value}`" for key, value in payload["closure"].items())
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
