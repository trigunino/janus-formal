from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z4_two_sector_carrier_tangent_projection_gate import build_payload as tangent_payload


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_two_sector_carrier_degenerate_closure_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_two_sector_carrier_degenerate_closure_gate.json")


def build_payload() -> dict:
    tangent = tangent_payload()
    closure = bool(tangent["closure_recommended"])
    return {
        "status": "janus-z4-two-sector-carrier-degenerate-closure-gate",
        "current_two_sector_source_closed_as_carrier_degenerate": closure,
        "reason": "carrier_A_s_tangent",
        "full_two_sector_parallel_fraction": tangent["parallel_fraction_full_two_sector"],
        "dominant_tangent_direction": tangent["dominant_tangent_direction_full_two_sector"],
        "variables_gate_preserved": True,
        "conservation_bianchi_gate_preserved": True,
        "initial_mode_gate_preserved": True,
        "linear_evolution_gate_preserved": True,
        "stability_gate_preserved": True,
        "source_level_regeneration_trace_preserved": True,
        "Planck_trial_forbidden": True,
        "Planck_trial_allowed": False,
        "spectra_generation_allowed": False,
        "profiling_forbidden": True,
        "profiling_allowed": False,
        "retuning_forbidden": True,
        "retuning_allowed": False,
        "candidate_promotion_allowed": False,
        "next_required_gate": "P0EFTJanusZ4TwoSectorSourceConstructionAuditGate",
        "profiled_planck_candidate": False,
        "full_planck_validation": False,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z4 Two-Sector Carrier-Degenerate Closure Gate",
        "",
        f"Closed as carrier-degenerate: `{payload['current_two_sector_source_closed_as_carrier_degenerate']}`",
        f"Reason: `{payload['reason']}`",
        f"Full parallel: `{payload['full_two_sector_parallel_fraction']}`",
        f"Planck forbidden: `{payload['Planck_trial_forbidden']}`",
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
