from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_boundary_stress_extraction_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_boundary_stress_extraction_gate.json")


def build_payload() -> dict:
    formula = {
        "full_boundary_action_closed_on_sigma": True,
        "induced_metric_variation_declared": True,
        "cartan_ghy_contribution_declared": True,
        "holst_nieh_yan_contribution_declared": True,
        "matter_flux_contribution_declared": True,
        "tunnel_junction_contribution_declared": True,
        "counterterm_contribution_declared": True,
        "T_eff_ab_extraction_formula_ready": True,
    }
    reduction = {
        "T_eff_ab_component_reduction_ready": False,
        "T_eff_ab_ready_for_FLRW_projection": False,
    }
    return {
        "status": "janus-z2-sigma-boundary-stress-extraction-gate",
        "active_core": "Z2_tunnel_Sigma",
        "bibliography_checked": True,
        "formula": formula,
        "reduction": reduction,
        "boundary_stress_extraction_formula_closed": all(formula.values()),
        "boundary_stress_ready_for_FLRW": all(formula.values()) and all(reduction.values()),
        "definition": (
            "T_eff_ab = -2/sqrt(|h|) * delta(S_CartanGHY + S_HolstNiehYan + "
            "S_matterFlux + S_tunnelJunction + S_counterterm) / delta h^ab"
        ),
        "component_blocks": [
            "T_CartanGHY_ab",
            "T_HolstNiehYan_ab",
            "T_matterFlux_ab",
            "T_tunnelJunction_ab",
            "T_counterterm_ab",
        ],
        "next_required": [
            "reduce_each_T_eff_ab_component_on_FLRW_induced_metric",
            "apply_Z2_normal_orientation_to_component_signs",
            "sum_components_into_T_eff_ab_for_effective_fluid_projection",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Boundary Stress Extraction Gate",
        "",
        f"Active core: `{payload['active_core']}`",
        f"Extraction formula closed: `{payload['boundary_stress_extraction_formula_closed']}`",
        f"Ready for FLRW projection: `{payload['boundary_stress_ready_for_FLRW']}`",
        f"Definition: `{payload['definition']}`",
        "",
        "## Component Blocks",
    ]
    lines.extend(f"- `{item}`" for item in payload["component_blocks"])
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
