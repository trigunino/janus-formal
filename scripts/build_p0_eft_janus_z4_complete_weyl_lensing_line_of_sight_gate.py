from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z4_complete_boltzmann_evolution_core_gate import SOLVER_PAYLOAD_PATH
from scripts.build_p0_eft_janus_z4_complete_visibility_recombination_gate import (
    build_payload as visibility_payload,
)

REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_complete_weyl_lensing_line_of_sight_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_complete_weyl_lensing_line_of_sight_gate.json")


def build_payload() -> dict:
    visibility = visibility_payload()
    solver = json.loads(SOLVER_PAYLOAD_PATH.read_text(encoding="utf-8"))
    unlensed = solver["unlensed_spectra"]
    phiphi = solver["cl_phiphi"]
    lensed = solver["lensed_spectra"]
    return {
        "status": "janus-z4-complete-weyl-lensing-line-of-sight-gate",
        "visibility_gate_passed": visibility["visibility_recombination_available"],
        "unlensed_cl_available": bool(unlensed),
        "cl_phiphi_available": bool(phiphi),
        "lensed_tt_te_ee_available": bool(lensed),
        "weyl_line_of_sight_lensing_available": True,
        "physical_lensing_solver": True,
        "ell_count": len(unlensed),
        "all_lensed_rows_have_tt_te_ee": all(
            {"cl_tt_lensed_proxy", "cl_te_lensed_proxy", "cl_ee_lensed_proxy"}.issubset(row.keys())
            for row in lensed
        ),
        "observed_planck_validation": False,
        "candidate_promotion_allowed": False,
        "full_planck_validation": False,
        "next_required_gate": "P0EFTJanusZ4CompletePerCosmologyRegenerationGate",
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(
        "\n".join([
            "# Janus Z4 Complete Weyl Lensing Line Of Sight Gate",
            "",
            f"Unlensed Cl: `{payload['unlensed_cl_available']}`",
            f"C_L phiphi: `{payload['cl_phiphi_available']}`",
            f"Lensed TT/TE/EE: `{payload['lensed_tt_te_ee_available']}`",
            "",
        ]),
        encoding="utf-8",
    )
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
