from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_pure_math_closure_audit_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_pure_math_closure_audit_gate.json")


def build_payload() -> dict:
    aps = {
        "target": "APS/Pin global theorem for eta_H = -2",
        "refined_gate": "p0_eft_janus_z4_aps_index_package_obligation_gate",
        "scaffold_complete": True,
        "local_trace_transport_closed": True,
        "spectrum_pairing_interface_closed": True,
        "kernel_trivialization_interface_closed": True,
        "global_index_theorem_proved_without_axioms": False,
        "remaining_axioms": [
            "pin_minus_lift_squared_minus_one",
            "aps_boundary_projector_fredholm",
            "eta_zero_mode_cancellation_global",
            "no_parity_anomaly_global",
            "trace_regularization_standard_global",
        ],
    }
    orbifold = {
        "target": "global orbifold 2:1 theorem for a_sigma = 2/3",
        "refined_gate": "p0_eft_janus_z4_orbifold_cover_ratio_obligation_gate",
        "scaffold_complete": True,
        "local_holonomy_transport_closed": True,
        "integer_flux_law_interface_closed": True,
        "orientation_rule_interface_closed": True,
        "global_orbifold_theorem_proved_without_axioms": False,
        "remaining_axioms": [
            "global_euler_holonomy_class_computed",
            "volume_cover_ratio_two_to_one",
            "global_volume_ratio_unique_two_to_one",
        ],
    }
    action = {
        "target": "unique Janus/Z4/Holst action-to-equations derivation",
        "refined_gates": [
            "p0_eft_janus_z4_nonlinear_boundary_variation_obligation_gate",
            "p0_eft_janus_z4_nonlinear_el_residual_obligation_gate",
            "p0_eft_janus_z4_gauge_fixing_variation_uniqueness_gate",
            "p0_eft_janus_z4_ward_atomic_closure_gate",
        ],
        "scaffold_complete": True,
        "bulk_palatini_variation_declared": True,
        "boundary_variation_inserted": True,
        "rank_one_source_recovered_interface": True,
        "ward_closure_interface": True,
        "unique_action_full_variation_proved_without_axioms": False,
        "remaining_axioms": [
            "full_nonlinear_boundary_variation_closed",
            "common_obstruction_vanishes",
            "ward_closure_ready",
            "gauge_fixing_variation_unique",
            "action_to_cmb_equations_transport_unique",
        ],
    }
    all_closed = bool(
        aps["global_index_theorem_proved_without_axioms"]
        and orbifold["global_orbifold_theorem_proved_without_axioms"]
        and action["unique_action_full_variation_proved_without_axioms"]
    )
    return {
        "status": "janus-z4-pure-math-closure-audit-gate",
        "aps_pin": aps,
        "orbifold_2_to_1": orbifold,
        "unique_action": action,
        "hard_external_theorem_target_registry": "p0_eft_janus_z4_hard_external_theorem_target_registry",
        "pure_math_model_closed_without_axioms": all_closed,
        "full_cosmology_prediction_ready_no_fit": all_closed,
        "cmb_validation_allowed_from_math_closure": all_closed,
        "next_required_gate": "prove_remaining_global_theorems_or_keep_axiomatic_scaffold",
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z4 Pure Math Closure Audit Gate",
        "",
        f"Pure math closed without axioms: `{payload['pure_math_model_closed_without_axioms']}`",
        f"No-fit ready: `{payload['full_cosmology_prediction_ready_no_fit']}`",
        "",
    ]
    for key in ("aps_pin", "orbifold_2_to_1", "unique_action"):
        block = payload[key]
        lines.extend([
            f"## {block['target']}",
            f"- refined gate: `{block.get('refined_gate', ', '.join(block.get('refined_gates', [])))}`",
            f"- scaffold complete: `{block['scaffold_complete']}`",
            f"- proved without axioms: `{block.get('global_index_theorem_proved_without_axioms', block.get('global_orbifold_theorem_proved_without_axioms', block.get('unique_action_full_variation_proved_without_axioms')))}`",
            "- remaining axioms:",
        ])
        lines.extend(f"  - `{item}`" for item in block["remaining_axioms"])
        lines.append("")
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
