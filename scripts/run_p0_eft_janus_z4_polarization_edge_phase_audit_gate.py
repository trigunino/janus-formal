from __future__ import annotations

import json
import sys
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.run_p0_eft_janus_z4_official_planck_polarization_source_delta_trial import (
    SUBCHANNELS,
    _diagnostics,
    _load_rows,
    _run_likelihood,
    _write_spectra,
)
from scripts.run_p0_eft_janus_z4_official_planck_lensing_shape_delta_trial import LIKELIHOODS


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_polarization_edge_phase_audit_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_polarization_edge_phase_audit_gate.json")
EXTENDED_LAMBDA_E_GRID = (-8.0e-2, -6.0e-2, -5.0e-2, -4.0e-2, -3.5e-2, -3.0e-2, -2.5e-2, -2.0e-2, -1.5e-2, -1.0e-2, -6.0e-3, -4.0e-3, -2.0e-3, 0.0, 2.0e-3, 4.0e-3, 8.0e-3)


def _channel_delta(row: dict, baseline: dict) -> dict[str, float]:
    finite = row.get("finite_channel_chi2", {})
    base = baseline.get("finite_channel_chi2", {})
    return {name: float(value - base[name]) for name, value in finite.items() if name in base}


def _curvature(lambdas: list[float], deltas: list[float | None], best_index: int | None) -> float | None:
    if best_index is None or best_index <= 0 or best_index >= len(lambdas) - 1:
        return None
    y0, y1, y2 = deltas[best_index - 1], deltas[best_index], deltas[best_index + 1]
    if y0 is None or y1 is None or y2 is None:
        return None
    x0, x1, x2 = lambdas[best_index - 1], lambdas[best_index], lambdas[best_index + 1]
    left = (y1 - y0) / (x1 - x0)
    right = (y2 - y1) / (x2 - x1)
    return float(2.0 * (right - left) / (x2 - x0))


def _monotonic_response(deltas: list[float | None]) -> bool:
    vals = [x for x in deltas if x is not None]
    if len(vals) < 3:
        return False
    return bool(all(a >= b for a, b in zip(vals, vals[1:])) or all(a <= b for a, b in zip(vals, vals[1:])))


def _phase_ok(diagnostics: dict) -> bool:
    return bool(
        diagnostics["TE_sign_check"]
        and abs(diagnostics["TE_zero_shift_1"]) < 0.01
        and abs(diagnostics["TE_zero_shift_2"]) < 0.01
        and abs(diagnostics["TE_zero_shift_3"]) < 0.01
        and abs(diagnostics["EE_peak_shift_1"]) < 0.02
        and abs(diagnostics["EE_peak_shift_2"]) < 0.02
        and abs(diagnostics["EE_peak_shift_3"]) < 0.02
        and diagnostics["TT_delta_when_lambda_E_changes"] == 0.0
        and diagnostics["Cphiphi_delta_when_lambda_E_changes"] == 0.0
    )


def _run_subchannel(rows: list[dict[str, float]], subchannel: str, run_official: bool) -> dict:
    spectra_paths = {str(lam): str(_write_spectra(rows, subchannel, lam)) for lam in EXTENDED_LAMBDA_E_GRID}
    diagnostics = {str(lam): _diagnostics(rows, subchannel, lam) for lam in EXTENDED_LAMBDA_E_GRID}
    trial_rows = {}
    if run_official:
        for lam in EXTENDED_LAMBDA_E_GRID:
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
        row["incremental_delta_chi2_over_temperature_only"] = (
            float(total - baseline_total)
            if total is not None and baseline_total is not None
            else None
        )
        row["incremental_delta_chi2_by_channel"] = _channel_delta(row, baseline)
    deltas = [
        trial_rows.get(str(lam), {}).get("incremental_delta_chi2_over_temperature_only")
        for lam in EXTENDED_LAMBDA_E_GRID
    ]
    finite = [(i, x) for i, x in enumerate(deltas) if x is not None]
    best_index = min(finite, key=lambda item: item[1])[0] if finite else None
    best_lambda = EXTENDED_LAMBDA_E_GRID[best_index] if best_index is not None else None
    best_diag = diagnostics.get(str(best_lambda), {}) if best_lambda is not None else {}
    best_edge = bool(best_index in (0, len(EXTENDED_LAMBDA_E_GRID) - 1)) if best_index is not None else True
    best_phase_ok = _phase_ok(best_diag) if best_diag else False
    return {
        "spectra_paths": spectra_paths,
        "diagnostics": diagnostics,
        "trial_rows": trial_rows,
        "best_lambda_E": str(best_lambda) if best_lambda is not None else None,
        "best_incremental_delta_chi2": deltas[best_index] if best_index is not None else None,
        "best_is_scan_edge": best_edge,
        "local_curvature_detected": _curvature(list(EXTENDED_LAMBDA_E_GRID), deltas, best_index),
        "monotonic_response": _monotonic_response(deltas),
        "full_extended_scan_perturbative_validity_passed": bool(all(_phase_ok(row) for row in diagnostics.values())),
        "TE_EE_phase_guard_passed_at_best": best_phase_ok,
        "TT_invariant_under_lambda_E": bool(all(row["TT_delta_when_lambda_E_changes"] == 0.0 for row in diagnostics.values())),
        "C_phi_phi_invariant_under_lambda_E": bool(all(row["Cphiphi_delta_when_lambda_E_changes"] == 0.0 for row in diagnostics.values())),
    }


def build_payload(run_official: bool = False) -> dict:
    rows = _load_rows()
    subchannels = {name: _run_subchannel(rows, name, run_official) for name in SUBCHANNELS}
    finite = {
        name: row["best_incremental_delta_chi2"]
        for name, row in subchannels.items()
        if row["best_incremental_delta_chi2"] is not None
    }
    best_subchannel = min(finite, key=finite.get) if finite else None
    best = subchannels.get(best_subchannel, {}) if best_subchannel else {}
    bracketed = bool(best and not best["best_is_scan_edge"])
    phase_ok = bool(best and best["TE_EE_phase_guard_passed_at_best"] and best["TT_invariant_under_lambda_E"] and best["C_phi_phi_invariant_under_lambda_E"])
    gate = bool(run_official and bracketed and phase_ok and best.get("best_incremental_delta_chi2", 0.0) < 0.0)
    return {
        "status": "janus-z4-polarization-edge-phase-audit-gate",
        "lambda_T_fixed": -8.0e-3,
        "extended_lambda_E_grid": list(EXTENDED_LAMBDA_E_GRID),
        "direct_Cl_patch": False,
        "native_toy_los_used": False,
        "recombination_delta_enabled": False,
        "visibility_delta_enabled": False,
        "background_projection_changed": False,
        "primordial_delta_enabled": False,
        "lensing_delta_enabled": False,
        "deltaSlip_Z4": "explicit_zero_until_derived",
        "available_planck_channels_only": True,
        "missing_highl_TE_EE_standalone_clik": True,
        "official_likelihood_requested": run_official,
        "official_likelihood_executed": bool(run_official),
        "subchannel_results": subchannels,
        "best_summary": {
            "best_subchannel": best_subchannel,
            "best_lambda_E": best.get("best_lambda_E") if best else None,
            "best_incremental_delta_chi2": best.get("best_incremental_delta_chi2") if best else None,
            "best_is_scan_edge": best.get("best_is_scan_edge") if best else None,
            "monotonic_response": best.get("monotonic_response") if best else None,
            "local_curvature_detected": best.get("local_curvature_detected") if best else None,
            "best_point_phase_guard_passed": best.get("TE_EE_phase_guard_passed_at_best") if best else None,
            "full_extended_scan_perturbative_validity_passed": best.get("full_extended_scan_perturbative_validity_passed") if best else None,
        },
        "polarization_edge_phase_audit_gate_passed": gate,
        "joint_acoustic_polarization_consistency_allowed": gate,
        "theta2_quadrupole_closure_gate_recommended": bool(not gate and best_subchannel == "Theta2_quadrupole_response"),
        "next_required_action": (
            "open AcousticPolarizationJointConsistencyGate"
            if gate
            else "do not open joint gate; derive Theta2QuadrupoleClosureGate or lambda_E normalization"
        ),
    }


def write_reports(run_official: bool = True) -> dict:
    payload = build_payload(run_official=run_official)
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2, sort_keys=True), encoding="utf-8")
    lines = [
        "# Janus Z4 Polarization Edge Phase Audit Gate",
        "",
        f"Gate passed: `{payload['polarization_edge_phase_audit_gate_passed']}`",
        f"Best summary: `{payload['best_summary']}`",
        f"Theta2 closure recommended: `{payload['theta2_quadrupole_closure_gate_recommended']}`",
        "",
        payload["next_required_action"],
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(run_official=True), indent=2))
