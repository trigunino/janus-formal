from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z4_complete_boltzmann_evolution_core_gate import SOLVER_PAYLOAD_PATH
from scripts.build_p0_eft_janus_z4_complete_per_cosmology_regeneration_gate import (
    build_payload as regeneration_payload,
)

REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_complete_likelihood_ready_theory_vector_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_complete_likelihood_ready_theory_vector_gate.json")
THEORY_VECTOR_PATH = Path("outputs/reports/p0_eft_janus_z4_complete_likelihood_ready_theory_vector.json")


def build_payload() -> dict:
    regeneration = regeneration_payload()
    solver = json.loads(SOLVER_PAYLOAD_PATH.read_text(encoding="utf-8"))
    vector = {
        "kind": "janus_z4_complete_cmb_theory_vector",
        "units": "dimensionless_proxy_Cl",
        "ell": [row["ell"] for row in solver["lensed_spectra"]],
        "cl_tt": [row["cl_tt_lensed_proxy"] for row in solver["lensed_spectra"]],
        "cl_te": [row["cl_te_lensed_proxy"] for row in solver["lensed_spectra"]],
        "cl_ee": [row["cl_ee_lensed_proxy"] for row in solver["lensed_spectra"]],
        "cl_phiphi": [row["cl_phiphi"] for row in solver["cl_phiphi"]],
        "provenance": solver["provenance"],
    }
    THEORY_VECTOR_PATH.write_text(json.dumps(vector, indent=2), encoding="utf-8")
    ready = bool(regeneration["per_cosmology_regeneration_passed"] and len(vector["ell"]) > 0)
    return {
        "status": "janus-z4-complete-likelihood-ready-theory-vector-gate",
        "theory_vector_path": str(THEORY_VECTOR_PATH),
        "likelihood_ready_theory_vector_available": ready,
        "theory_vector_units": vector["units"],
        "requires_cl_convention_calibration": vector["units"] == "dimensionless_proxy_Cl",
        "per_cosmology_regeneration_passed": regeneration["per_cosmology_regeneration_passed"],
        "contains_lensed_tt_te_ee": all(key in vector for key in ("cl_tt", "cl_te", "cl_ee")),
        "contains_cl_phiphi": "cl_phiphi" in vector,
        "observed_likelihood_diagnostic_allowed": ready,
        "observed_planck_validation": False,
        "candidate_promotion_allowed": False,
        "full_planck_validation": False,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(
        "\n".join([
            "# Janus Z4 Complete Likelihood Ready Theory Vector Gate",
            "",
            f"Theory vector available: `{payload['likelihood_ready_theory_vector_available']}`",
            f"Observed diagnostic allowed: `{payload['observed_likelihood_diagnostic_allowed']}`",
            f"Full Planck validation: `{payload['full_planck_validation']}`",
            "",
        ]),
        encoding="utf-8",
    )
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
