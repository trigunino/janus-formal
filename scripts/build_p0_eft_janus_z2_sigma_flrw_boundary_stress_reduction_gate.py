from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z2_sigma_cartan_ghy_flrw_projection_gate import (
    build_payload as build_cartan_projection_payload,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_flrw_boundary_stress_reduction_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_flrw_boundary_stress_reduction_gate.json")


def build_payload() -> dict:
    cartan_projection = build_cartan_projection_payload()
    setup = {
        "boundary_stress_extraction_formula_closed": True,
        "induced_FLRW_sigma_metric_declared": True,
        "Z2_normal_orientation_declared": True,
    }
    component_reductions = {
        "cartan_GHY_FLRW_reduced": True,
        "holst_Nieh_Yan_FLRW_reduced": False,
        "matter_flux_FLRW_reduced": False,
        "tunnel_junction_FLRW_reduced": True,
        "counterterm_FLRW_reduced": False,
    }
    scale_factor_functions = {
        "cartan_GHY_Delta_Ks_of_a_ready": cartan_projection["scale_factor"][
            "Delta_Ks_of_a_ready"
        ],
        "cartan_GHY_Delta_Ktau_of_a_ready": cartan_projection["scale_factor"][
            "Delta_Ktau_of_a_ready"
        ],
        "tunnel_junction_Delta_Ks_of_a_ready": False,
        "tunnel_junction_Delta_Ktau_of_a_ready": False,
        "tunnel_junction_non_circular_partition_ready": False,
    }
    projection = {
        "component_signs_fixed_by_Z2_normal": False,
        "T_eff_ab_ready_for_FLRW_projection": False,
    }
    return {
        "status": "janus-z2-sigma-flrw-boundary-stress-reduction-gate",
        "active_core": "Z2_tunnel_Sigma",
        "bibliography_checked": True,
        "bibliography_result": (
            "Generic Brown-York/thin-shell FLRW reduction methods exist, but no direct "
            "Janus Z2/Sigma component reduction was found."
        ),
        "setup": setup,
        "component_reductions": component_reductions,
        "scale_factor_functions": scale_factor_functions,
        "projection": projection,
        "upstream_frontiers": {
            "cartan_ghy_flrw_projection": {
                "gate": cartan_projection["status"],
                "algebraic_ready": cartan_projection[
                    "cartan_GHY_FLRW_algebraic_projection_ready"
                ],
                "scale_factor_ready": cartan_projection[
                    "cartan_GHY_FLRW_scale_factor_closure_ready"
                ],
                "scale_factor": cartan_projection["scale_factor"],
            },
        },
        "all_component_reductions_ready": all(component_reductions.values()),
        "flrw_boundary_stress_reduction_ready": (
            all(setup.values())
            and all(component_reductions.values())
            and all(scale_factor_functions.values())
            and all(projection.values())
        ),
        "blocked_components": [
            name for name, ready in component_reductions.items() if not ready
        ],
        "next_required": [
            "derive_Cartan_GHY_DeltaK_s_and_DeltaK_tau_as_functions_of_a",
            "reduce_Holst_Nieh_Yan_boundary_stress_on_FLRW_Sigma",
            "reduce_matter_flux_boundary_stress_on_FLRW_Sigma",
            "derive_tunnel_junction_DeltaK_s_and_DeltaK_tau_as_functions_of_a",
            "define_non_circular_partition_between_CartanGHY_and_tunnel_junction",
            "fix_component_signs_from_Z2_normal_orientation",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma FLRW Boundary Stress Reduction Gate",
        "",
        f"Active core: `{payload['active_core']}`",
        f"Bibliography checked: `{payload['bibliography_checked']}`",
        f"All component reductions ready: `{payload['all_component_reductions_ready']}`",
        f"FLRW boundary stress reduction ready: `{payload['flrw_boundary_stress_reduction_ready']}`",
        "",
        "## Blocked Components",
    ]
    lines.extend(f"- `{item}`" for item in payload["blocked_components"])
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
