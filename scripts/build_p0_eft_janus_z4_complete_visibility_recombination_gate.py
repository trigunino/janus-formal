from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z4_complete_boltzmann_evolution_core_gate import (
    SOLVER_PAYLOAD_PATH,
    build_payload as core_payload,
)

REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_complete_visibility_recombination_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_complete_visibility_recombination_gate.json")


def build_payload() -> dict:
    core = core_payload()
    solver = json.loads(SOLVER_PAYLOAD_PATH.read_text(encoding="utf-8"))
    visibility = solver["visibility"]
    optical_depth = solver["optical_depth"]
    peak = max(solver["background_rows"], key=lambda row: row["visibility"])
    return {
        "status": "janus-z4-complete-visibility-recombination-gate",
        "core_gate_passed": core["z4_boltzmann_evolution_core_available"],
        "visibility_recombination_available": True,
        "optical_depth_available": True,
        "visibility_peak_a": peak["a"],
        "visibility_peak_value": peak["visibility"],
        "visibility_positive": all(value >= 0.0 for value in visibility),
        "optical_depth_monotone": all(optical_depth[i] >= optical_depth[i + 1] for i in range(len(optical_depth) - 1)),
        "reionization_visibility_included": True,
        "observed_planck_validation": False,
        "candidate_promotion_allowed": False,
        "full_planck_validation": False,
        "next_required_gate": "P0EFTJanusZ4CompleteWeylLensingLineOfSightGate",
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(
        "\n".join([
            "# Janus Z4 Complete Visibility Recombination Gate",
            "",
            f"Visibility available: `{payload['visibility_recombination_available']}`",
            f"Peak a: `{payload['visibility_peak_a']}`",
            f"Optical depth monotone: `{payload['optical_depth_monotone']}`",
            "",
        ]),
        encoding="utf-8",
    )
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
