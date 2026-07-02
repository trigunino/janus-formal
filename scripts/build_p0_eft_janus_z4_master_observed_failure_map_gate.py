from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z4_master_observed_nonoverlap_accounting_gate import build_payload as accounting_payload


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_master_observed_failure_map_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_master_observed_failure_map_gate.json")


def build_payload() -> dict:
    accounting = accounting_payload()
    deltas = accounting["delta_chi2_by_channel"]
    finite = {key: float(value) for key, value in deltas.items() if value is not None}
    ranked = sorted(finite.items(), key=lambda item: item[1], reverse=True)
    highl_total = sum(finite.get(key, 0.0) for key in ("highl_TT", "highl_TE", "highl_EE"))
    lowl_total = sum(finite.get(key, 0.0) for key in ("lowl_TT", "lowl_EE"))
    lensing = finite.get("lensing", 0.0)
    highl_dominates = highl_total > 1000.0 and highl_total > abs(lowl_total) + abs(lensing)
    return {
        "status": "janus-z4-master-observed-failure-map-gate",
        "observed_master_branch_rejected": accounting["observed_master_branch_rejected"],
        "ranked_channel_deltas": ranked,
        "dominant_failure_channel": ranked[0][0] if ranked else None,
        "highl_decomposed_total": highl_total,
        "lowl_total": lowl_total,
        "lensing_delta": lensing,
        "highl_failure_dominates": highl_dominates,
        "low_l_failure_dominates": bool(abs(lowl_total) > highl_total),
        "lensing_rescue_insufficient": bool(lensing < 0.0 and abs(lensing) < highl_total),
        "failure_class": "high_l_acoustic_shape_failure" if highl_dominates else "undetermined",
        "candidate_promotion_allowed": False,
        "observational_claim_allowed": False,
        "full_planck_validation": False,
        "next_required_gate": "revise_master_highl_acoustic_shape_before_any_promotion",
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z4 Master Observed Failure Map Gate",
        "",
        f"Failure class: `{payload['failure_class']}`",
        f"Dominant channel: `{payload['dominant_failure_channel']}`",
        f"High-l total: `{payload['highl_decomposed_total']}`",
        f"Lensing delta: `{payload['lensing_delta']}`",
        f"Promotion allowed: `{payload['candidate_promotion_allowed']}`",
        f"Next gate: `{payload['next_required_gate']}`",
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
