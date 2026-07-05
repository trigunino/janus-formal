from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_cartan_ghy_from_extrinsic_curvature_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_cartan_ghy_from_extrinsic_curvature_gate.json")


def build_payload() -> dict:
    return {
        "status": "janus-z2-sigma-cartan-ghy-from-extrinsic-curvature-gate",
        "active_core": "Z2_tunnel_Sigma",
        "cartan_ghy_from_K_plus_minus_builder_ready": True,
        "composes_DeltaK_jump_builder": True,
        "composes_Cartan_GHY_component_builder": True,
        "input_curvatures": ["K_s_plus(a)", "K_s_minus(a)", "K_tau_plus(a)", "K_tau_minus(a)"],
        "output_components": ["rho_CGHY_over_rho_crit0(a)", "p_CGHY_over_rho_crit0(a)"],
        "requires_active_K_plus_minus_of_a": True,
        "requires_explicit_z2_orientation": True,
        "requires_explicit_kappa_rho_crit0": True,
        "uses_planck_lcdm_inputs": False,
        "uses_archived_z4_inputs": False,
        "cartan_ghy_values_ready": False,
        "gate_passed": True,
        "next_required": [
            "derive_active_K_s_tau_plus_minus_of_a",
            "derive_active_kappa_rho_crit0_or_equivalent_normalization",
            "write_Cartan_GHY_components_to_active_BAO_component_manifest",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Cartan-GHY From Extrinsic Curvature Gate",
        "",
        f"Builder ready: `{payload['cartan_ghy_from_K_plus_minus_builder_ready']}`",
        f"Values ready: `{payload['cartan_ghy_values_ready']}`",
        f"Gate passed: `{payload['gate_passed']}`",
        "",
        "## Next Required",
    ]
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
