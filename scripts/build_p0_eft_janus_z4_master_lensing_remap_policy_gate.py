from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z4_master_unlensed_lensed_split_gate import (
    build_payload as split_payload,
)

REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_master_lensing_remap_policy_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_master_lensing_remap_policy_gate.json")


def build_payload() -> dict:
    split = split_payload()
    observed_ready = bool(split["unlensed_lensed_split_available"] and split["lensed_remap_generated"])
    return {
        "status": "janus-z4-master-lensing-remap-policy-gate",
        "unlensed_lensed_split_available": split["unlensed_lensed_split_available"],
        "unlensed_spectra_path": split["unlensed_spectra_path"],
        "lensed_spectra_path": split["lensed_spectra_path"],
        "lensing_kernel_path": split["lensing_kernel_path"],
        "lensed_remap_generated": split["lensed_remap_generated"],
        "lensed_remap_policy": split["lensed_remap_policy"],
        "physical_lensing_solver": split["physical_lensing_solver"],
        "lensed_total_available_for_future_observed_diagnostic": observed_ready,
        "policy_allows_future_observed_diagnostic": observed_ready,
        "policy_warning": "internal remap, not a physical CMB lensing solver" if not split["physical_lensing_solver"] else "physical remap",
        "observed_likelihood_allowed_now": False,
        "planck_retry_allowed_now": False,
        "candidate_promotion_allowed": False,
        "retuning_allowed": False,
        "full_planck_validation": False,
        "next_required_gate": "P0EFTJanusZ4MasterFutureObservedPlanckDiagnosticReadinessGate",
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z4 Master Lensing Remap Policy Gate",
        "",
        f"Future observed diagnostic allowed by policy: `{payload['policy_allows_future_observed_diagnostic']}`",
        f"Policy warning: `{payload['policy_warning']}`",
        f"Observed likelihood allowed now: `{payload['observed_likelihood_allowed_now']}`",
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
