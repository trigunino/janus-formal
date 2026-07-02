from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_gauge_fixing_variation_uniqueness_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_gauge_fixing_variation_uniqueness_gate.json")


def build_payload() -> dict:
    obligations = {
        "gauge_fixing_variation_inserted": True,
        "gauge_condition_declared": True,
        "residual_gauge_freedom_classified": True,
        "gauge_choice_independent_of_observation": True,
        "residual_gauge_freedom_removed_by_janus_geometry": False,
        "gauge_fixed_boundary_variation_unique": False,
    }
    ready_keys = (
        "gauge_fixing_variation_inserted",
        "gauge_condition_declared",
        "residual_gauge_freedom_classified",
        "gauge_choice_independent_of_observation",
    )
    return {
        "status": "janus-z4-gauge-fixing-variation-uniqueness-gate",
        "gauge_obligations": obligations,
        "gauge_fixing_scaffold_ready": all(obligations[key] for key in ready_keys),
        "gauge_fixing_variation_unique": all(obligations.values()),
        "remaining_gauge_obligations": [
            key for key, value in obligations.items() if not value
        ],
        "pure_math_model_closed_without_axioms": False,
        "full_cosmology_prediction_ready_no_fit": False,
        "next_required_gate": "derive_residual_gauge_removal_from_janus_geometry",
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z4 Gauge-Fixing Variation Uniqueness Gate",
        "",
        f"Gauge scaffold ready: `{payload['gauge_fixing_scaffold_ready']}`",
        f"Gauge-fixing variation unique: `{payload['gauge_fixing_variation_unique']}`",
        "",
        "## Remaining gauge obligations",
    ]
    lines.extend(f"- `{item}`" for item in payload["remaining_gauge_obligations"])
    REPORT_PATH.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
