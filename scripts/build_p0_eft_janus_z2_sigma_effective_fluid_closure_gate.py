from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from janus_lab.z2_sigma_flrw_component_manifest import load_active_z2sigma_flrw_component_manifest


FLRW_COMPONENT_MANIFEST_PATH = Path("outputs/active_z2_sigma/flrw_components.json")
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_effective_fluid_closure_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_effective_fluid_closure_gate.json")


def build_payload() -> dict:
    flrw_manifest_exists = FLRW_COMPONENT_MANIFEST_PATH.exists()
    flrw_manifest_valid = False
    flrw_manifest_error = None
    if flrw_manifest_exists:
        try:
            load_active_z2sigma_flrw_component_manifest(FLRW_COMPONENT_MANIFEST_PATH)
            flrw_manifest_valid = True
        except Exception as exc:
            flrw_manifest_error = str(exc)
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
        "T_eff_ab_FLRW_component_reduction_ready": flrw_manifest_valid,
        "T_eff_ab_ready_for_FLRW_projection": flrw_manifest_valid,
        "induced_flrw_sigma_metric_declared": True,
        "perfect_fluid_projection_declared": True,
        "rho_eff_projection_formula_ready": True,
        "p_eff_projection_formula_ready": True,
    }
    numeric = {
        "strict_effective_fluid_component_assembler_ready": True,
        "assembler_requires_active_FLRW_component_rho_p": True,
        "rho_eff_Z2Sigma_of_a_ready": flrw_manifest_valid,
        "p_eff_Z2Sigma_of_a_ready": flrw_manifest_valid,
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
        "flrw_component_manifest_status": {
            "path": str(FLRW_COMPONENT_MANIFEST_PATH),
            "exists": flrw_manifest_exists,
            "valid": flrw_manifest_valid,
            "validation_error": flrw_manifest_error,
        },
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
            "supply_active_Cartan_Holst_matter_flux_counterterm_rho_p_components",
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
        f"FLRW component manifest: `{payload['flrw_component_manifest_status']['path']}`",
        f"FLRW component manifest valid: `{payload['flrw_component_manifest_status']['valid']}`",
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
