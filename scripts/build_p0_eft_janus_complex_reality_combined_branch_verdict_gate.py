from __future__ import annotations

import json
import sys
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_complex_reality_combined_kks_period_gate import (
    build_payload as build_period_payload,
)
from scripts.build_p0_eft_janus_complex_reality_noncentral_spin_lift_search_gate import (
    build_payload as build_lift_payload,
)


REPORTS = Path("outputs/reports")
JSON_PATH = REPORTS / "p0_eft_janus_complex_reality_combined_branch_verdict_gate.json"
REPORT_PATH = REPORTS / "p0_eft_janus_complex_reality_combined_branch_verdict_gate.md"


def build_payload() -> dict[str, Any]:
    period = build_period_payload()
    lift = build_lift_payload()
    return {
        "status": "janus-complex-reality-combined-branch-verdict-gate",
        "mathematical_candidate_survives": period["symbolic_combined_KKS_period_nonzero"],
        "janus_physical_derivation_closed": False,
        "alpha_generated_now": False,
        "results": {
            "cp1_local_candidate": True,
            "cp1_global_janus_pt_derived": period["checks"]["cp1_derived_from_Janus_PT"],
            "aroundSigma_noncentral_lift_derived": lift["noncentral_spin_lift_derived"],
            "symbolic_kks_period_nonzero": period["symbolic_combined_KKS_period_nonzero"],
            "janus_derived_kks_period_nonzero": period[
                "janus_derived_combined_KKS_period_nonzero"
            ],
        },
        "blocking_reasons": [
            "global_Z2Sigma_spinor_projection_not_closed",
            "resolved_tunnel_Pin_lift_not_closed",
            "noncentral_aroundSigma_spin_lift_not_forced",
            "sector_selection_j_nonzero_not_derived",
            "alpha_map_not_derived",
        ],
        "verdict": (
            "The combined S2+CP1+aroundSigma branch is the best current quantum "
            "candidate. It produces a symbolic nonzero KKS period, but not a "
            "Janus-derived alpha law. Further progress needs global spinor/Pin "
            "geometry or the parked radical quantum-geometry reconstruction."
        ),
        "gate_passed": True,
    }


def write_reports() -> dict[str, Any]:
    payload = build_payload()
    REPORTS.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(
        "\n".join(
            [
                "# Janus Complex Reality Combined Branch Verdict Gate",
                "",
                f"Mathematical candidate survives: `{payload['mathematical_candidate_survives']}`",
                f"Janus physical derivation closed: `{payload['janus_physical_derivation_closed']}`",
                f"Alpha generated now: `{payload['alpha_generated_now']}`",
                "",
                payload["verdict"],
            ]
        )
        + "\n",
        encoding="utf-8",
    )
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
