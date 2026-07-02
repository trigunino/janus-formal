from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_nonoverlapping_likelihood_accounting_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_nonoverlapping_likelihood_accounting_gate.json")
TRIAL_JSON = Path("outputs/reports/p0_eft_janus_z4_closed_boltzmann_candidate_highl_decomposition_trial.json")


def _load(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8")) if path.exists() else {}


def _value(payload: dict, key: str) -> float:
    value = payload.get(key)
    if value is None:
        raise ValueError(f"Missing {key} in {TRIAL_JSON}")
    return float(value)


def build_payload() -> dict:
    trial = _load(TRIAL_JSON)
    highl_tt = _value(trial, "delta_chi2_highl_TT")
    highl_te = _value(trial, "delta_chi2_highl_TE")
    highl_ee = _value(trial, "delta_chi2_highl_EE")
    highl_ttteee = _value(trial, "delta_chi2_highl_TTTEEE")
    lowl_tt = _value(trial, "delta_chi2_lowl_TT")
    lowl_ee = _value(trial, "delta_chi2_lowl_EE")
    lensing = _value(trial, "delta_chi2_lensing")
    overlapping_total = _value(trial, "delta_chi2_total")
    nonoverlap_combined = highl_ttteee + lowl_tt + lowl_ee + lensing
    nonoverlap_decomposed = highl_tt + highl_te + highl_ee + lowl_tt + lowl_ee + lensing
    return {
        "status": "janus-z4-nonoverlapping-likelihood-accounting-gate",
        "source_trial": str(TRIAL_JSON),
        "delta_chi2_highl_TT": highl_tt,
        "delta_chi2_highl_TE": highl_te,
        "delta_chi2_highl_EE": highl_ee,
        "delta_chi2_highl_TTTEEE": highl_ttteee,
        "delta_chi2_lowl_TT": lowl_tt,
        "delta_chi2_lowl_EE": lowl_ee,
        "delta_chi2_lensing": lensing,
        "legacy_overlapping_total": overlapping_total,
        "nonoverlapping_total_combined_highl": nonoverlap_combined,
        "nonoverlapping_total_decomposed_highl": nonoverlap_decomposed,
        "combined_highl_total_defined": True,
        "decomposed_highl_total_defined": True,
        "overlapping_highl_sum_forbidden": True,
        "reported_total_uses_one_highl_basis_only": True,
        "legacy_overlapping_total_marked_diagnostic_only": True,
        "nonoverlapping_combined_improves": nonoverlap_combined < 0.0,
        "nonoverlapping_decomposed_improves": nonoverlap_decomposed < 0.0,
        "TE_standalone_cost_small": 0.0 <= highl_te < 0.1,
        "EE_standalone_not_degraded": highl_ee <= 0.0,
        "accounting_gate_passed": bool(
            nonoverlap_combined < 0.0
            and nonoverlap_decomposed < 0.0
            and 0.0 <= highl_te < 0.1
            and highl_ee <= 0.0
        ),
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2, sort_keys=True), encoding="utf-8")
    lines = [
        "# Janus Z4 Non-Overlapping Likelihood Accounting Gate",
        "",
        f"Gate passed: `{payload['accounting_gate_passed']}`",
        f"Legacy overlapping total: `{payload['legacy_overlapping_total']}`",
        f"Non-overlapping combined high-l total: `{payload['nonoverlapping_total_combined_highl']}`",
        f"Non-overlapping decomposed high-l total: `{payload['nonoverlapping_total_decomposed_highl']}`",
        "",
        "The overlapping total is diagnostic only and must not be used as a likelihood total.",
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
