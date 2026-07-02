from __future__ import annotations

import json
import sys
from dataclasses import replace
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT / "src"))
    sys.path.insert(0, str(ROOT))

from janus_lab.z4_cmb_solver import solve_z4_cmb
from janus_lab.z4_regenerative_camb_provider import CosmologyPoint
from scripts.build_p0_eft_janus_z4_complete_weyl_lensing_line_of_sight_gate import (
    build_payload as lensing_payload,
)

REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_complete_per_cosmology_regeneration_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_complete_per_cosmology_regeneration_gate.json")


def build_payload() -> dict:
    lensing = lensing_payload()
    base = CosmologyPoint()
    variants = {
        "ombh2": replace(base, ombh2=base.ombh2 * 1.01),
        "omch2": replace(base, omch2=base.omch2 * 0.99),
        "H0": replace(base, H0=base.H0 + 0.5),
        "tau": replace(base, tau=base.tau + 0.005),
        "As": replace(base, As=base.As * 1.02),
        "ns": replace(base, ns=base.ns + 0.005),
    }
    base_payload = solve_z4_cmb(base)
    checks = {}
    for name, cosmology in variants.items():
        payload = solve_z4_cmb(cosmology)
        checks[name] = {
            "cosmology_hash_changed": payload["provenance"]["cosmology_hash"] != base_payload["provenance"]["cosmology_hash"],
            "theory_vector_hash_changed": payload["provenance"]["theory_vector_hash"] != base_payload["provenance"]["theory_vector_hash"],
            "per_cosmology_regenerated": payload["provenance"]["per_cosmology_regenerated"],
        }
    passed = all(row["cosmology_hash_changed"] and row["theory_vector_hash_changed"] and row["per_cosmology_regenerated"] for row in checks.values())
    return {
        "status": "janus-z4-complete-per-cosmology-regeneration-gate",
        "lensing_gate_passed": lensing["weyl_line_of_sight_lensing_available"],
        "per_cosmology_regeneration_passed": passed,
        "regeneration_checks": checks,
        "cache_provenance_available": True,
        "observed_planck_validation": False,
        "candidate_promotion_allowed": False,
        "full_planck_validation": False,
        "next_required_gate": "P0EFTJanusZ4CompleteLikelihoodReadyTheoryVectorGate",
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(
        "\n".join([
            "# Janus Z4 Complete Per-Cosmology Regeneration Gate",
            "",
            f"Regeneration passed: `{payload['per_cosmology_regeneration_passed']}`",
            f"Planck validation: `{payload['observed_planck_validation']}`",
            "",
        ]),
        encoding="utf-8",
    )
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
