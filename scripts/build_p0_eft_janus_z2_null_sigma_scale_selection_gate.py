from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.janus_lab.z2_null_sigma_action_variation import (
    null_sigma_action_variation_payload,
)
from src.janus_lab.z2_null_sigma_variation_reduction import (
    null_sigma_variation_reduction_payload,
)
from src.janus_lab.z2_null_sigma_pt_joint import null_sigma_pt_joint_payload
from scripts.build_p0_eft_janus_z2_null_sigma_barrabes_israel_pt_antiequivariance_gate import (
    build_payload as build_pt_antiequivariance,
)
from src.janus_lab.z2_null_sigma_generator_normalization import (
    null_sigma_generator_normalization_payload,
)
from scripts.build_p0_eft_janus_z2_null_sigma_stationarity_scale_obstruction_gate import (
    build_payload as build_stationarity_obstruction,
)
from scripts.build_p0_eft_janus_z2_null_sigma_state_charge_to_mass_bridge_gate import (
    build_payload as build_state_charge_to_mass,
)
from scripts.build_p0_eft_janus_z2_null_sigma_global_noether_souriau_mass_bridge_gate import (
    build_payload as build_global_noether_souriau_mass,
)
from scripts.build_p0_eft_janus_z2_null_sigma_bulk_rs_to_global_mass_gate import (
    build_payload as build_bulk_rs_to_global_mass,
)
from scripts.build_p0_eft_janus_z2_null_sigma_llbrane_tension_to_rs_gate import (
    build_payload as build_llbrane_tension_to_rs,
)
from scripts.build_p0_eft_janus_z2_null_sigma_mass_charge_to_rs_gate import (
    build_payload as build_mass_charge_to_rs,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_null_sigma_scale_selection_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_null_sigma_scale_selection_gate.json")


def build_payload() -> dict:
    action = null_sigma_action_variation_payload()
    variation = null_sigma_variation_reduction_payload()
    joint = null_sigma_pt_joint_payload()
    pt_bi = build_pt_antiequivariance()
    generator = null_sigma_generator_normalization_payload()
    stationarity = build_stationarity_obstruction()
    state_charge = build_state_charge_to_mass()
    llbrane = build_llbrane_tension_to_rs()
    bulk_rs = build_bulk_rs_to_global_mass()
    global_mass = build_global_noether_souriau_mass()
    mass_charge = build_mass_charge_to_rs()
    closure = {
        "null_boundary_density_identified": True,
        "radial_variation_reduced": variation["bulk_null_density_variation_reduced"],
        "density_depends_on_Rs": True,
        "stationarity_equation_sets_Rs": stationarity[
            "null_stationarity_selects_absolute_Rs"
        ],
        "PT_joint_term_ready": joint["PT_joint_term_ready"],
        "null_shell_stress_mapping_ready": pt_bi["active_stress_mapping_ready"],
        "conditional_PT_stress_mapping_ready": pt_bi["conditional_stress_mapping_ready"],
        "active_PT_stress_mapping_ready": pt_bi["active_stress_mapping_ready"],
        "null_generator_rescaling_quotiented": generator[
            "null_generator_rescaling_quotiented"
        ],
        "absolute_Rs_selected": mass_charge["absolute_Rs_selected"],
    }
    return {
        "status": "janus-z2-null-sigma-scale-selection-gate",
        "active_core": "Z2_tunnel_Sigma",
        "branch": "Z2_null_Sigma_PT_bridge",
        "density": action["null_boundary_density"],
        "radial_reduction": variation["radial_reduction"],
        "PT_joint": joint["PT_joint_model"],
        "conditional_barrabes_israel": {
            "status": pt_bi["status"],
            "conditional_stress_mapping_ready": pt_bi[
                "conditional_stress_mapping_ready"
            ],
            "active_stress_mapping_ready": pt_bi["active_stress_mapping_ready"],
            "scale_selection_ready": pt_bi["scale_selection_ready"],
        },
        "generator_normalization": {
            "route": generator["route"],
            "normalization_condition": generator["normalization_condition"],
            "boost_parameter_alpha_fixed": generator["boost_parameter_alpha_fixed"],
            "rescaling_quotiented": generator[
                "null_generator_rescaling_quotiented"
            ],
        },
        "closure": closure,
        "null_scale_selection_ready": all(closure.values()),
        "stationarity_obstruction": stationarity["obstruction"],
        "state_charge_to_mass": {
            "status": state_charge["status"],
            "state_charge_mass_available": state_charge[
                "state_charge_mass_available"
            ],
            "M_bridge_available": state_charge["M_bridge_available"],
            "next_required": state_charge["next_required"],
        },
        "llbrane_tension_to_Rs": {
            "status": llbrane["status"],
            "extension_status": llbrane["extension_status"],
            "llbrane_tension_available": llbrane["llbrane_tension_available"],
            "bulk_Rs_solution_available": llbrane["bulk_Rs_solution_available"],
            "formulae": llbrane["formulae"],
            "next_required": llbrane["next_required"],
        },
        "bulk_rs_to_global_mass": {
            "status": bulk_rs["status"],
            "bulk_Rs_solution_available": bulk_rs["bulk_Rs_solution_available"],
            "global_mass_solution_available": bulk_rs[
                "global_mass_solution_available"
            ],
            "next_required": bulk_rs["next_required"],
        },
        "global_noether_souriau_mass": {
            "status": global_mass["status"],
            "global_mass_solution_available": global_mass[
                "global_mass_solution_available"
            ],
            "M_bridge_available": global_mass["M_bridge_available"],
            "souriau_PT_sign_law": global_mass["souriau_PT_sign_law"],
            "next_required": global_mass["next_required"],
        },
        "mass_charge_to_Rs": {
            "status": mass_charge["status"],
            "mass_charge_available": mass_charge["mass_charge_available"],
            "absolute_Rs_selected": mass_charge["absolute_Rs_selected"],
            "next_required": mass_charge["next_required"],
        },
        "interpretation": (
            "The null-boundary density, PT joint term, Barrabes-Israel stress slots, "
            "and null-generator normalization are now reduced. The remaining blocker "
            "is structural: the reduced null/PT action contains no internal length "
            "scale and therefore does not select an absolute R_s."
        ),
        "blocked_by": [key for key, ok in closure.items() if not ok],
        "forbidden_shortcuts": [
            "do_not_set_Rs_to_one_as_physical_length",
            "do_not_use_null_density_as_stationarity_equation_without_joint_terms",
            "do_not_ignore_null_generator_rescaling",
        ],
        "gate_passed": True,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2 Null Sigma Scale Selection Gate",
        "",
        payload["interpretation"],
        "",
        f"Null scale selection ready: `{payload['null_scale_selection_ready']}`",
        f"Density: `{payload['density']['symbolic']}`",
        "",
        "## Blocked By",
    ]
    lines.extend(f"- `{item}`" for item in payload["blocked_by"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
