from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_full_action_atomic_closure_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_full_action_atomic_closure_gate.json")


def build_payload() -> dict:
    obligations = {
        "linearized_action_ready": True,
        "determinant_measure_physical_ready": True,
        "full_boundary_action_closed": False,
        "assembly_scaffold_ready": True,
        "nonlinear_euler_lagrange_residual_vanishing": False,
        "ward_closure_ready": False,
    }
    closed = all(obligations.values())
    return {
        "status": "janus-z4-full-action-atomic-closure-gate",
        "atomic_action_obligations": obligations,
        "unique_action_variation_closed": closed,
        "closed_sub_obligations": [
            key for key, value in obligations.items() if value
        ],
        "remaining_action_obligations": [
            key for key, value in obligations.items() if not value
        ],
        "pure_math_model_closed_without_axioms": False,
        "full_cosmology_prediction_ready_no_fit": False,
        "next_required_gate": "close_measure_boundary_nonlinear_ward_obligations",
        "refined_boundary_gate": "p0_eft_janus_z4_nonlinear_boundary_variation_obligation_gate",
        "refined_el_residual_gate": "p0_eft_janus_z4_nonlinear_el_residual_obligation_gate",
        "refined_gauge_gate": "p0_eft_janus_z4_gauge_fixing_variation_uniqueness_gate",
        "refined_ward_gate": "p0_eft_janus_z4_ward_atomic_closure_gate",
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z4 Full Action Atomic Closure Gate",
        "",
        f"Unique action variation closed: `{payload['unique_action_variation_closed']}`",
        "",
        "## Remaining action obligations",
    ]
    lines.extend(f"- `{item}`" for item in payload["remaining_action_obligations"])
    REPORT_PATH.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
