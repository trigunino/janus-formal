from __future__ import annotations

import csv
import json
import sys
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z4_master_likelihood_handshake_gate import build_payload as handshake_payload


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_master_diagnostic_likelihood_trial_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_master_diagnostic_likelihood_trial_gate.json")
CHANNELS = ("cl_tt", "cl_te", "cl_ee")


def _read(path: str) -> dict[str, np.ndarray]:
    with Path(path).open(newline="", encoding="utf-8") as handle:
        rows = list(csv.DictReader(handle))
    return {key: np.asarray([float(row[key]) for row in rows], dtype=float) for key in ("ell", *CHANNELS)}


def _pseudo_chi2(base: np.ndarray, cand: np.ndarray) -> float:
    floor = 0.05 * (float(np.sqrt(np.mean(np.square(base)))) or 1.0)
    sigma = 0.25 * np.maximum(np.abs(base), floor)
    residual = cand - base
    return float(np.sum(np.square(residual / sigma)))


def build_payload() -> dict:
    handshake = handshake_payload()
    base = _read(handshake["baseline_spectra_path"])
    cand = _read(handshake["candidate_spectra_path"])
    rows = {}
    for channel in CHANNELS:
        rows[channel] = {
            "pseudo_chi2": _pseudo_chi2(base[channel], cand[channel]),
            "finite": bool(np.all(np.isfinite(cand[channel]))),
            "max_abs_fractional_delta": float(
                np.max(np.abs((cand[channel] - base[channel]) / np.maximum(np.abs(base[channel]), 1.0e-30)))
            ),
        }
    total = float(sum(row["pseudo_chi2"] for row in rows.values()))
    trial_passed = bool(
        handshake["likelihood_handshake_passed"]
        and all(row["finite"] for row in rows.values())
        and np.isfinite(total)
    )
    return {
        "status": "janus-z4-master-diagnostic-likelihood-trial-gate",
        "likelihood_handshake_passed": handshake["likelihood_handshake_passed"],
        "trial_kind": "internal_gr_reference_pseudo_likelihood",
        "uses_observed_planck_data": False,
        "uses_official_planck_likelihood": False,
        "pseudo_chi2_by_channel": rows,
        "pseudo_chi2_total": total,
        "nonoverlap_accounting": True,
        "diagnostic_likelihood_trial_passed": trial_passed,
        "master_derived_signal_passed_carrier_projection": handshake["carrier_threshold_passed"],
        "official_planck_trial_allowed": False,
        "candidate_promotion_allowed": False,
        "observational_claim_allowed": False,
        "next_required_gate": "P0EFTJanusZ4MasterOfficialLikelihoodPolicyGate",
        "profiled_planck_candidate": False,
        "full_planck_validation": False,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z4 Master Diagnostic Likelihood Trial Gate",
        "",
        f"Trial kind: `{payload['trial_kind']}`",
        f"Pseudo chi2 total: `{payload['pseudo_chi2_total']}`",
        f"Diagnostic trial passed: `{payload['diagnostic_likelihood_trial_passed']}`",
        f"Uses official Planck: `{payload['uses_official_planck_likelihood']}`",
        f"Official Planck allowed: `{payload['official_planck_trial_allowed']}`",
        f"Next gate: `{payload['next_required_gate']}`",
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
