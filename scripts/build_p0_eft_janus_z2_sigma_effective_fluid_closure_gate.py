from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_effective_fluid_closure_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_effective_fluid_closure_gate.json")


def build_payload() -> dict:
    bibliography = {
        "israel_junction_conditions_checked": True,
        "brown_york_stress_tensor_checked": True,
        "cosmological_thin_shell_fluid_checked": True,
        "direct_janus_z2_sigma_rho_p_formula_found": False,
    }
    structural = {
        "projected_sigma_stress_tensor_derived": True,
        "z2_tunnel_junction_condition_derived": True,
        "T_eff_ab_extraction_formula_ready": True,
        "T_eff_ab_FLRW_component_reduction_ready": False,
        "T_eff_ab_ready_for_FLRW_projection": False,
        "induced_flrw_sigma_metric_declared": True,
        "perfect_fluid_projection_declared": True,
        "rho_eff_projection_formula_ready": True,
        "p_eff_projection_formula_ready": True,
    }
    numeric = {
        "rho_eff_Z2Sigma_of_a_ready": False,
        "p_eff_Z2Sigma_of_a_ready": False,
    }
    return {
        "status": "janus-z2-sigma-effective-fluid-closure-gate",
        "active_core": "Z2_tunnel_Sigma",
        "bibliography": bibliography,
        "primary_sources_checked": [
            "Israel junction conditions / thin-shell formalism",
            "Brown-York stress tensor from boundary variation",
            "cosmological thin-shell effective density and pressure examples",
        ],
        "structural": structural,
        "numeric": numeric,
        "effective_fluid_structural_projection_ready": (
            structural["projected_sigma_stress_tensor_derived"]
            and structural["z2_tunnel_junction_condition_derived"]
            and structural["T_eff_ab_extraction_formula_ready"]
            and structural["induced_flrw_sigma_metric_declared"]
            and structural["perfect_fluid_projection_declared"]
            and structural["rho_eff_projection_formula_ready"]
            and structural["p_eff_projection_formula_ready"]
        ),
        "effective_fluid_numeric_closure_ready": all(structural.values()) and all(numeric.values()),
        "projection_definitions": {
            "rho_eff": "rho_eff_Z2Sigma(a) = T_eff_ab u^a u^b after Z2/Sigma projection",
            "p_eff": "p_eff_Z2Sigma(a) = spatial_trace(T_eff_ab) / 3 after Z2/Sigma projection",
        },
        "next_required": [
            "pass_z2_sigma_flrw_boundary_stress_reduction_gate",
            "insert_FLRW_induced_metric_and_Z2_normal_orientation",
            "reduce_rho_eff_and_p_eff_to_functions_of_scale_factor",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Effective Fluid Closure Gate",
        "",
        f"Active core: `{payload['active_core']}`",
        f"Structural projection ready: `{payload['effective_fluid_structural_projection_ready']}`",
        f"Numeric closure ready: `{payload['effective_fluid_numeric_closure_ready']}`",
        f"Direct Janus formula found in bibliography: `{payload['bibliography']['direct_janus_z2_sigma_rho_p_formula_found']}`",
        "",
        "## Projection Definitions",
    ]
    lines.extend(f"- `{key}`: `{value}`" for key, value in payload["projection_definitions"].items())
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
