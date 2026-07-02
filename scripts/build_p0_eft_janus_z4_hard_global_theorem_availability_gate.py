from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_hard_global_theorem_availability_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_hard_global_theorem_availability_gate.json")


def build_payload() -> dict:
    theorems = {
        "aps_pin_global_index": {
            "paper_theorem_exists": True,
            "lean_mathlib_import_available": False,
            "project_specific_geometry_match_proved": False,
            "can_close_now": False,
            "reason": "APS/Pin index theory exists mathematically, but no direct Lean/mathlib APS-Pin import was found; Janus bulk geometry matching remains unproved.",
        },
        "orbifold_two_to_one": {
            "paper_theorem_exists": False,
            "lean_mathlib_import_available": False,
            "project_specific_geometry_match_proved": False,
            "can_close_now": False,
            "reason": "Janus Z2 2:1 volume/branching classification is project-specific; no generic imported theorem closes it.",
        },
        "unique_janus_z4_holst_action": {
            "paper_theorem_exists": False,
            "lean_mathlib_import_available": False,
            "project_specific_geometry_match_proved": False,
            "can_close_now": False,
            "reason": "Unique Janus/Z4/Holst action variation is project-specific and still has nonlinear/boundary/Ward closure obligations.",
        },
    }
    all_importable = all(row["lean_mathlib_import_available"] and row["project_specific_geometry_match_proved"] for row in theorems.values())
    return {
        "status": "janus-z4-hard-global-theorem-availability-gate",
        "theorems": theorems,
        "all_hard_global_theorems_importable_or_closed": all_importable,
        "pure_math_model_closed_without_axioms": False,
        "full_cosmology_prediction_ready_no_fit": False,
        "next_required_gate": "project_specific_geometry_match_proofs",
        "external_target_registry": "p0_eft_janus_z4_hard_external_theorem_target_registry",
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z4 Hard Global Theorem Availability Gate",
        "",
        f"All importable/closed: `{payload['all_hard_global_theorems_importable_or_closed']}`",
        "",
    ]
    for name, row in payload["theorems"].items():
        lines.extend([
            f"## `{name}`",
            f"- paper theorem exists: `{row['paper_theorem_exists']}`",
            f"- Lean/mathlib import available: `{row['lean_mathlib_import_available']}`",
            f"- project geometry match proved: `{row['project_specific_geometry_match_proved']}`",
            f"- can close now: `{row['can_close_now']}`",
            f"- reason: {row['reason']}",
            "",
        ])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
