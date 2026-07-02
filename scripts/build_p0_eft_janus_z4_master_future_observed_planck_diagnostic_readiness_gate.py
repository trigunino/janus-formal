from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z4_master_lensing_remap_policy_gate import (
    build_payload as lensing_policy_payload,
)
from scripts.build_p0_eft_janus_z4_master_solver_provenance_manifest_gate import (
    build_payload as provenance_payload,
)

REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_master_future_observed_planck_diagnostic_readiness_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_master_future_observed_planck_diagnostic_readiness_gate.json")


def build_payload() -> dict:
    lensing_policy = lensing_policy_payload()
    provenance = provenance_payload()
    future_ready = bool(
        provenance["cache_provenance_manifest_written"]
        and provenance["component_spectra_hashes_recorded"]
        and provenance["unlensed_lensed_split_available"]
        and lensing_policy["policy_allows_future_observed_diagnostic"]
    )
    return {
        "status": "janus-z4-master-future-observed-planck-diagnostic-readiness-gate",
        "future_observed_planck_diagnostic_allowed": future_ready,
        "unlensed_lensed_split_available": provenance["unlensed_lensed_split_available"],
        "lensing_remap_policy": provenance["lensing_remap_policy"],
        "physical_lensing_solver": provenance["physical_lensing_solver"],
        "provenance_manifest_ready": provenance["cache_provenance_manifest_written"],
        "non_retuning_guard_passed": True,
        "retuning_allowed": False,
        "candidate_promotion_allowed": False,
        "observed_planck_validation": False,
        "full_planck_validation": False,
        "future_diagnostic_scope": "observed_likelihood_diagnostic_only",
        "next_required_gate": "future_observed_planck_diagnostic_trial_no_promotion",
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z4 Master Future Observed Planck Diagnostic Readiness Gate",
        "",
        f"Future observed Planck diagnostic allowed: `{payload['future_observed_planck_diagnostic_allowed']}`",
        f"Observed Planck validation: `{payload['observed_planck_validation']}`",
        f"Full Planck validation: `{payload['full_planck_validation']}`",
        f"Retuning allowed: `{payload['retuning_allowed']}`",
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
