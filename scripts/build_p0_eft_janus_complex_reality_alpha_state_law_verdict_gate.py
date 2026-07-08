from __future__ import annotations

import json
import sys
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_complex_reality_eq131_kks_projection_gate import (
    build_payload as build_eq131_payload,
)
from scripts.build_p0_eft_janus_complex_reality_prequantization_integrality_gate import (
    build_payload as build_prequantization_payload,
)
from scripts.build_p0_eft_janus_complex_reality_source_formula_curation_gate import (
    build_payload as build_source_payload,
)


REPORTS = Path("outputs/reports")
JSON_PATH = REPORTS / "p0_eft_janus_complex_reality_alpha_state_law_verdict_gate.json"
REPORT_PATH = REPORTS / "p0_eft_janus_complex_reality_alpha_state_law_verdict_gate.md"


def build_payload() -> dict[str, Any]:
    source = build_source_payload()
    eq131 = build_eq131_payload()
    preq = build_prequantization_payload()

    checks = {
        "source_formula_curated": source["formula_curation_ready"],
        "eq131_projection_consistent": eq131[
            "kks_ready_term_preserves_antihermitian_M"
        ],
        "kks_prequantization_ready": preq["route_ready"],
        "prequantization_integral_ready": preq[
            "prequantization_integrality_ready"
        ],
        "mass_charge_lattice_derived": False,
        "alpha_state_sector_law_derived": False,
        "global_alpha_map_derived": False,
    }
    alpha_prediction_ready = all(checks.values())
    return {
        "status": "janus-complex-reality-alpha-state-law-verdict-gate",
        "checks": checks,
        "alpha_prediction_ready": alpha_prediction_ready,
        "alpha_generated_now": False,
        "branch_status": "frozen_pending_state_law",
        "allowed_interpretation": (
            "Complex reality supplies a sourced coadjoint/Souriau scaffold and a "
            "symbolic KKS candidate. It does not yet derive the boundary cycle, "
            "prequantization lattice, primitive sector law, or alpha map."
        ),
        "blocked_outputs": [
            "unique_alpha_m_prediction",
            "mass_charge_lattice_prediction",
            "primitive_sector_selection",
            "no_fit_background_normalization",
        ],
        "still_missing": [key for key, ok in checks.items() if not ok],
        "gate_passed": True,
    }


def write_reports() -> dict[str, Any]:
    payload = build_payload()
    REPORTS.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(
        "\n".join(
            [
                "# Janus Complex Reality Alpha State Law Verdict Gate",
                "",
                f"Alpha prediction ready: `{payload['alpha_prediction_ready']}`",
                f"Alpha generated now: `{payload['alpha_generated_now']}`",
                f"Branch status: `{payload['branch_status']}`",
                "",
                payload["allowed_interpretation"],
                "",
                "## Still Missing",
                "",
                *[f"- `{item}`" for item in payload["still_missing"]],
            ]
        )
        + "\n",
        encoding="utf-8",
    )
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
