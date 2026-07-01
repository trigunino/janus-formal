from __future__ import annotations

import json
import sys
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.run_p0_eft_janus_z4_official_planck_acoustic_driving_delta_trial import (
    LIKELIHOODS,
    _diagnostics,
    _load_rows,
    _run_likelihood,
    _write_spectra,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_acoustic_phase_consistency_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_acoustic_phase_consistency_gate.json")
REFINED_LAMBDAS = (-3.0e-2, -2.0e-2, -1.5e-2, -1.2e-2, -1.0e-2, -8.0e-3, -6.0e-3, -4.0e-3, -2.0e-3, 0.0, 2.0e-3, 4.0e-3)
COMPONENT = "early_isw_only"


def _channel_delta(row: dict, baseline: dict) -> dict[str, float]:
    finite = row.get("finite_channel_chi2", {})
    base = baseline.get("finite_channel_chi2", {})
    return {name: float(value - base[name]) for name, value in finite.items() if name in base}


def _curvature(lambdas: list[float], deltas: list[float | None], best_index: int) -> float | None:
    if best_index <= 0 or best_index >= len(lambdas) - 1:
        return None
    y0, y1, y2 = deltas[best_index - 1], deltas[best_index], deltas[best_index + 1]
    if y0 is None or y1 is None or y2 is None:
        return None
    x0, x1, x2 = lambdas[best_index - 1], lambdas[best_index], lambdas[best_index + 1]
    left = (y1 - y0) / (x1 - x0)
    right = (y2 - y1) / (x2 - x1)
    return float(2.0 * (right - left) / (x2 - x0))


def _monotonic_near_zero(lambdas: list[float], deltas: list[float | None]) -> bool:
    near = [(x, y) for x, y in zip(lambdas, deltas) if y is not None and -4.0e-3 <= x <= 4.0e-3]
    if len(near) < 4:
        return False
    ys = [y for _, y in near]
    return bool(all(a >= b for a, b in zip(ys, ys[1:])) or all(a <= b for a, b in zip(ys, ys[1:])))


def build_payload(run_official: bool = False) -> dict:
    rows = _load_rows()
    spectra_paths = {str(lam): str(_write_spectra(rows, COMPONENT, lam)) for lam in REFINED_LAMBDAS}
    diagnostics = {str(lam): _diagnostics(rows, COMPONENT, lam) for lam in REFINED_LAMBDAS}
    trial_rows = {}
    if run_official:
        for lam in REFINED_LAMBDAS:
            path = Path(spectra_paths[str(lam)])
            channels = {name: _run_likelihood(component, path) for name, component in LIKELIHOODS.items()}
            finite = {name: row["chi2"] for name, row in channels.items() if row["finite"]}
            trial_rows[str(lam)] = {
                "spectra_path": str(path),
                "channels": channels,
                "finite_channel_chi2": finite,
                "total_finite_chi2": float(sum(finite.values())) if finite else None,
            }
    baseline = trial_rows.get("0.0", {})
    baseline_total = baseline.get("total_finite_chi2")
    for row in trial_rows.values():
        total = row.get("total_finite_chi2")
        row["delta_chi2_total_available"] = (
            float(total - baseline_total)
            if total is not None and baseline_total is not None
            else None
        )
        row["delta_chi2_by_channel_available"] = _channel_delta(row, baseline)

    lambdas = [float(x) for x in REFINED_LAMBDAS]
    deltas = [trial_rows.get(str(x), {}).get("delta_chi2_total_available") for x in REFINED_LAMBDAS]
    finite_pairs = [(i, y) for i, y in enumerate(deltas) if y is not None]
    best_index = min(finite_pairs, key=lambda item: item[1])[0] if finite_pairs else None
    best_lambda = lambdas[best_index] if best_index is not None else None
    best_delta = deltas[best_index] if best_index is not None else None
    best_diag = diagnostics.get(str(best_lambda), {}) if best_lambda is not None else {}
    best_breakdown = trial_rows.get(str(best_lambda), {}).get("delta_chi2_by_channel_available") if best_lambda is not None else None
    lensing_delta = (best_breakdown or {}).get("lensing")
    edge = bool(best_index in (0, len(REFINED_LAMBDAS) - 1)) if best_index is not None else True
    te_ok = bool(best_diag.get("TE_sign_check", False) and abs(best_diag.get("TE_first_zero_shift", 1.0)) < 0.01 and abs(best_diag.get("TE_second_zero_shift", 1.0)) < 0.01)
    ee_pp_ok = bool(
        all(row["EE_max_delta"] == 0.0 and row["Cphiphi_max_delta"] == 0.0 for row in diagnostics.values())
    )
    lensing_subdominant = bool(
        lensing_delta is None
        or best_delta is None
        or abs(lensing_delta) < 0.25 * max(abs(best_delta), 1.0e-300)
    )
    gate = bool(run_official and best_delta is not None and te_ok and ee_pp_ok and not edge and lensing_subdominant)
    return {
        "status": "janus-z4-acoustic-phase-consistency-gate",
        "component": COMPONENT,
        "trial_type": "refined_effective_acoustic_temperature_source_delta",
        "not_full_z4_verdict": True,
        "backend": "camb_gr_plus_z4_delta",
        "direct_Cl_patch": False,
        "native_toy_los_used": False,
        "polarization_source_delta_enabled": False,
        "EE_unchanged_by_construction": True,
        "Cphiphi_unchanged_by_construction": True,
        "recombination_delta_enabled": False,
        "visibility_delta_enabled": False,
        "lambda_grid": list(REFINED_LAMBDAS),
        "official_likelihood_requested": run_official,
        "official_likelihood_executed": bool(trial_rows),
        "spectra_paths": spectra_paths,
        "diagnostics": diagnostics,
        "trial_rows": trial_rows,
        "best_lambda_refined": best_lambda,
        "delta_chi2_at_best": best_delta,
        "channel_breakdown_at_best": best_breakdown,
        "lensing_likelihood_delta_at_best": lensing_delta,
        "lensing_likelihood_delta_subdominant": lensing_subdominant,
        "lensing_likelihood_delta_warning": bool(lensing_delta is not None and abs(lensing_delta) > 1.0e-6),
        "local_curvature_estimate": _curvature(lambdas, deltas, best_index) if best_index is not None else None,
        "response_monotonic_near_zero": _monotonic_near_zero(lambdas, deltas),
        "edge_of_scan_best": edge,
        "TE_phase_guard_passed": te_ok,
        "EE_Cphiphi_frozen_guard_passed": ee_pp_ok,
        "acoustic_phase_consistency_gate_passed": gate,
        "polarization_source_delta_gate_allowed": gate,
        "next_required_action": (
            "open PolarizationSourceDeltaGate only if the non-edge refined optimum remains robust"
            if gate
            else "do not open polarization yet; refine lambda range or derive slip/phase correction"
        ),
    }


def write_reports(run_official: bool = True) -> dict:
    payload = build_payload(run_official=run_official)
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2, sort_keys=True), encoding="utf-8")
    lines = [
        "# Janus Z4 Acoustic Phase Consistency Gate",
        "",
        f"Gate passed: `{payload['acoustic_phase_consistency_gate_passed']}`",
        f"Best lambda: `{payload['best_lambda_refined']}`",
        f"Best delta chi2: `{payload['delta_chi2_at_best']}`",
        f"Edge-of-scan best: `{payload['edge_of_scan_best']}`",
        f"TE phase guard: `{payload['TE_phase_guard_passed']}`",
        f"EE/Cphiphi frozen guard: `{payload['EE_Cphiphi_frozen_guard_passed']}`",
        f"Lensing likelihood delta at best: `{payload['lensing_likelihood_delta_at_best']}`",
        f"Lensing likelihood delta subdominant: `{payload['lensing_likelihood_delta_subdominant']}`",
        f"Monotonic near zero: `{payload['response_monotonic_near_zero']}`",
        "",
        "## Channel Breakdown At Best",
    ]
    for key, value in (payload["channel_breakdown_at_best"] or {}).items():
        lines.append(f"- `{key}`: `{value}`")
    lines.extend(["", payload["next_required_action"], ""])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(run_official=True), indent=2))
