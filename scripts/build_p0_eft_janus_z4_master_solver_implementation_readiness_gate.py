from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z4_master_solver_provenance_manifest_gate import (
    build_payload as provenance_payload,
)

REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_master_solver_implementation_readiness_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_master_solver_implementation_readiness_gate.json")


def build_payload() -> dict:
    provenance = provenance_payload()
    solver_implemented = bool(
        provenance["shape_phase_damping_gate_ready"]
        and provenance["cache_provenance_manifest_written"]
        and provenance["component_spectra_hashes_recorded"]
        and provenance["calculator_payload_hash_recorded"]
        and provenance["unlensed_lensed_provenance_declared"]
    )
    return {
        "status": "janus-z4-master-solver-implementation-readiness-gate",
        "solver_implemented": solver_implemented,
        "solver_scope": "internal_diagnostic_cmb_generation_only",
        "internal_diagnostic_generation_ready": solver_implemented,
        "acoustic_calculator_component_spectra_ready": provenance["component_spectra_hashes_recorded"],
        "shape_phase_damping_diagnostics_ready": provenance["shape_phase_damping_gate_ready"],
        "cache_provenance_manifest_ready": provenance["cache_provenance_manifest_written"],
        "unlensed_lensed_provenance_declared": provenance["unlensed_lensed_provenance_declared"],
        "unlensed_lensed_split_available": provenance["unlensed_lensed_split_available"],
        "lensing_remap_policy": provenance["lensing_remap_policy"],
        "physical_lensing_solver": provenance["physical_lensing_solver"],
        "observed_planck_validation": False,
        "observed_likelihood_allowed": False,
        "candidate_promotion_allowed": False,
        "retuning_allowed": False,
        "full_planck_validation": False,
        "next_required_gate": "future_observational_gate_after_unlensed_or_source_backend_upgrade",
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z4 Master Solver Implementation Readiness Gate",
        "",
        f"Solver implemented: `{payload['solver_implemented']}`",
        f"Scope: `{payload['solver_scope']}`",
        f"Observed Planck validation: `{payload['observed_planck_validation']}`",
        f"Retuning allowed: `{payload['retuning_allowed']}`",
        f"Full Planck validation: `{payload['full_planck_validation']}`",
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
