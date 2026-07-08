from __future__ import annotations

import json
import sys
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_complex_reality_around_sigma_cp1_holonomy_action_gate import (
    build_payload as build_holonomy_payload,
)
from scripts.build_p0_eft_janus_complex_reality_cp1_from_janus_pt_gate import (
    build_payload as build_cp1_payload,
)


REPORTS = Path("outputs/reports")
JSON_PATH = REPORTS / "p0_eft_janus_complex_reality_combined_kks_period_gate.json"
REPORT_PATH = REPORTS / "p0_eft_janus_complex_reality_combined_kks_period_gate.md"


def build_payload() -> dict[str, Any]:
    cp1 = build_cp1_payload()
    holonomy = build_holonomy_payload()
    checks = {
        "cp1_KKS_period_symbolic": cp1["cp1_mathematical_candidate_ready"],
        "period_formula_nonzero_if_j_nonzero": True,
        "cp1_derived_from_Janus_PT": cp1["cp1_derived_from_Janus_PT"],
        "aroundSigma_action_on_CP1_derived": holonomy["aroundSigma_action_on_CP1_derived"],
        "sector_selection_law_derived": False,
        "j_nonzero_selected": False,
    }
    symbolic_combined_period_nonzero = (
        checks["cp1_KKS_period_symbolic"]
        and checks["period_formula_nonzero_if_j_nonzero"]
    )
    janus_combined_period_nonzero = symbolic_combined_period_nonzero and all(
        checks[key]
        for key in [
            "cp1_derived_from_Janus_PT",
            "aroundSigma_action_on_CP1_derived",
            "sector_selection_law_derived",
            "j_nonzero_selected",
        ]
    )
    return {
        "status": "janus-complex-reality-combined-kks-period-gate",
        "period_formula": "Integral_CP1 Omega_j = 4*pi*j",
        "prequantization": "2*j/hbar in Z",
        "checks": checks,
        "symbolic_combined_KKS_period_nonzero": symbolic_combined_period_nonzero,
        "janus_derived_combined_KKS_period_nonzero": janus_combined_period_nonzero,
        "alpha_generated_now": False,
        "verdict": (
            "The combined candidate has a symbolic nonzero KKS period if a "
            "nonzero CP1 spin label j is supplied. It is not a Janus-derived "
            "period yet because CP1, the aroundSigma action, and the nonzero "
            "sector selection are not derived."
        ),
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
                "# Janus Complex Reality Combined KKS Period Gate",
                "",
                f"Symbolic period nonzero: `{payload['symbolic_combined_KKS_period_nonzero']}`",
                f"Janus-derived period nonzero: `{payload['janus_derived_combined_KKS_period_nonzero']}`",
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
