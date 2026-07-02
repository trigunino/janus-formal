from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.run_p0_eft_janus_z4_official_planck_closed_boltzmann_acoustic_polarization_trial import (
    _load_rows,
    _run_likelihood_set,
    _write_spectra,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_closed_boltzmann_candidate_highl_decomposition_trial.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_closed_boltzmann_candidate_highl_decomposition_trial.json")
HANDSHAKE_JSON = Path("outputs/reports/p0_eft_janus_z4_standalone_teee_handshake_gate.json")
FROZEN_LAMBDA_T = -8.0e-3
FROZEN_LAMBDA_E = -2.0e-2


def _load(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8")) if path.exists() else {}


def _delta(candidate: dict, baseline: dict, channel: str) -> float | None:
    c = candidate.get("finite_channel_chi2", {}).get(channel)
    b = baseline.get("finite_channel_chi2", {}).get(channel)
    return float(c - b) if c is not None and b is not None else None


def build_payload(run_official: bool = False) -> dict:
    handshake = _load(HANDSHAKE_JSON)
    allowed = bool(handshake.get("closed_boltzmann_candidate_highl_decomposition_trial_allowed"))
    rows = _load_rows()
    baseline_path = _write_spectra(rows, 0.0, 0.0)
    candidate_path = _write_spectra(rows, FROZEN_LAMBDA_T, FROZEN_LAMBDA_E)
    baseline = _run_likelihood_set(baseline_path, bool(run_official and allowed))
    candidate = _run_likelihood_set(candidate_path, bool(run_official and allowed))
    channels = (
        "highl_TT",
        "highl_TE",
        "highl_EE",
        "highl_TTTEEE",
        "lowl_TT",
        "lowl_EE",
        "lensing",
    )
    deltas = {channel: _delta(candidate, baseline, channel) for channel in channels}
    finite = [value for value in deltas.values() if value is not None]
    return {
        "status": "janus-z4-closed-boltzmann-candidate-highl-decomposition-trial",
        "handshake_gate_passed": bool(handshake.get("standalone_teee_handshake_gate_passed")),
        "highl_decomposition_trial_allowed": allowed,
        "run_official_requested": run_official,
        "run_official_executed": bool(run_official and allowed),
        "backend": "camb_gr_plus_z4_delta",
        "lambda_T": FROZEN_LAMBDA_T,
        "lambda_E": FROZEN_LAMBDA_E,
        "candidate_rerun_unchanged": True,
        "no_parameter_retuning": True,
        "no_new_z4_physics": True,
        "baseline_spectra_path": str(baseline_path),
        "candidate_spectra_path": str(candidate_path),
        "baseline": baseline,
        "candidate": candidate,
        "delta_chi2_highl_TT": deltas["highl_TT"],
        "delta_chi2_highl_TE": deltas["highl_TE"],
        "delta_chi2_highl_EE": deltas["highl_EE"],
        "delta_chi2_highl_TTTEEE": deltas["highl_TTTEEE"],
        "delta_chi2_lowl_TT": deltas["lowl_TT"],
        "delta_chi2_lowl_EE": deltas["lowl_EE"],
        "delta_chi2_lensing": deltas["lensing"],
        "delta_chi2_total": float(sum(finite)) if len(finite) == len(channels) else None,
        "full_planck_validation": False,
    }


def write_reports(run_official: bool = True) -> dict:
    payload = build_payload(run_official=run_official)
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2, sort_keys=True), encoding="utf-8")
    lines = [
        "# Janus Z4 Closed-Boltzmann Candidate High-L Decomposition Trial",
        "",
        f"Handshake passed: `{payload['handshake_gate_passed']}`",
        f"Trial allowed: `{payload['highl_decomposition_trial_allowed']}`",
        f"Official run executed: `{payload['run_official_executed']}`",
        f"lambda_T: `{payload['lambda_T']}`",
        f"lambda_E: `{payload['lambda_E']}`",
        "",
        "## Delta chi2",
        "",
    ]
    for key in (
        "delta_chi2_highl_TT",
        "delta_chi2_highl_TE",
        "delta_chi2_highl_EE",
        "delta_chi2_highl_TTTEEE",
        "delta_chi2_lowl_TT",
        "delta_chi2_lowl_EE",
        "delta_chi2_lensing",
        "delta_chi2_total",
    ):
        lines.append(f"- `{key}`: `{payload[key]}`")
    lines.extend(["", "Full Planck validation remains false.", ""])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(run_official=True), indent=2))
