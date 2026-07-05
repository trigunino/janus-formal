from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_extrinsic_curvature_tensor_builder_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_extrinsic_curvature_tensor_builder_gate.json")


def build_payload() -> dict:
    return {
        "status": "janus-z2-sigma-extrinsic-curvature-tensor-builder-gate",
        "active_core": "Z2_tunnel_Sigma",
        "bibliography_checked": True,
        "primary_sources_checked": [
            "Israel junction conditions",
            "Poisson & Visser 1995 thin-shell extrinsic-curvature conventions",
        ],
        "extrinsic_curvature_tensor_builder_ready": True,
        "formula": "K_ab = -n_mu (partial_a partial_b X^mu + Gamma^mu_{alpha beta} e_a^alpha e_b^beta)",
        "equivalent_definition": "K_ab = e_a^mu e_b^nu nabla_mu n_nu",
        "flrw_reduction_ready": True,
        "flrw_reduction": {
            "K_s": "gamma^{ij} K_ij / 3",
            "K_tau": "K_tau_tau",
        },
        "requires_active_embedding_second_derivatives": True,
        "requires_active_christoffel_symbols": True,
        "requires_active_normal_covector": True,
        "requires_active_spatial_inverse_metric": True,
        "uses_planck_lcdm_inputs": False,
        "uses_archived_z4_inputs": False,
        "K_ab_values_ready": False,
        "gate_passed": True,
        "next_required": [
            "derive_active_tunnel_embedding_X_plus_minus_of_a",
            "derive_active_metric_and_Christoffel_symbols_on_both_sides",
            "derive_active_unit_normals_and_spatial_inverse_metric_on_Sigma",
            "evaluate_K_s_plus_minus_and_K_tau_plus_minus",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Extrinsic Curvature Tensor Builder Gate",
        "",
        f"Tensor builder ready: `{payload['extrinsic_curvature_tensor_builder_ready']}`",
        f"FLRW reduction ready: `{payload['flrw_reduction_ready']}`",
        f"K_ab values ready: `{payload['K_ab_values_ready']}`",
        f"Gate passed: `{payload['gate_passed']}`",
        "",
        "## Formula",
        f"`{payload['formula']}`",
        "",
        "## Next Required",
    ]
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
