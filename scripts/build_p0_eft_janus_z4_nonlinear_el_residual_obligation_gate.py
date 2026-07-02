from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z4_nonlinear_residual_factorization import (
    build_payload as build_factorization_payload,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_nonlinear_el_residual_obligation_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_nonlinear_el_residual_obligation_gate.json")


def build_payload() -> dict:
    factorization = build_factorization_payload()
    obligations = {
        "full_action_assembly_scaffold_ready": True,
        "rank_one_source_recovered": True,
        "residual_pair_factorized": factorization["residual_factorization_ready"],
        "determinant_reciprocal_weight_used": True,
        "common_obstruction_extracted": True,
        "common_obstruction_vanishes": factorization["obstruction_vanishing_derived"],
        "nonlinear_euler_lagrange_residual_vanishing": False,
    }
    closed = all(obligations.values())
    return {
        "status": "janus-z4-nonlinear-el-residual-obligation-gate",
        "factorization_status": factorization["status"],
        "common_obstruction": factorization["common_obstruction"],
        "el_residual_obligations": obligations,
        "nonlinear_el_residual_reduced_to_common_obstruction": all(
            obligations[key]
            for key in (
                "full_action_assembly_scaffold_ready",
                "rank_one_source_recovered",
                "residual_pair_factorized",
                "determinant_reciprocal_weight_used",
                "common_obstruction_extracted",
            )
        ),
        "nonlinear_el_residual_closed": closed,
        "remaining_el_obligations": [
            key for key, value in obligations.items() if not value
        ],
        "pure_math_model_closed_without_axioms": False,
        "full_cosmology_prediction_ready_no_fit": False,
        "next_required_gate": "derive_common_nonlinear_obstruction_vanishes",
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z4 Nonlinear EL Residual Obligation Gate",
        "",
        f"Reduced to common obstruction: `{payload['nonlinear_el_residual_reduced_to_common_obstruction']}`",
        f"Common obstruction: `{payload['common_obstruction']}`",
        f"Nonlinear EL residual closed: `{payload['nonlinear_el_residual_closed']}`",
        "",
        "## Remaining EL obligations",
    ]
    lines.extend(f"- `{item}`" for item in payload["remaining_el_obligations"])
    REPORT_PATH.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
