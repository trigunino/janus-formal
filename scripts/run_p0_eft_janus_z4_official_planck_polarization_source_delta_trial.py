from __future__ import annotations

import csv
import json
import sys
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z4_polarization_source_delta_gate import (
    LAMBDA_REF,
    SUBCHANNELS,
    build_payload as polarization_gate_payload,
)
from scripts.run_p0_eft_janus_z4_official_planck_acoustic_driving_delta_trial import (
    LIKELIHOODS,
    _diagnostics as temperature_diagnostics,
    _load_rows,
    _run_likelihood,
    _tag,
    _transfer_response,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_official_planck_polarization_source_delta_trial.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_official_planck_polarization_source_delta_trial.json")
SPECTRA_DIR = Path("outputs/reports/z4_polarization_source_delta_trial_spectra")
LAMBDA_E_GRID = (-2.0e-2, -1.5e-2, -1.2e-2, -1.0e-2, -8.0e-3, -6.0e-3, -4.0e-3, -2.0e-3, 0.0, 2.0e-3, 4.0e-3, 6.0e-3, 8.0e-3, 1.0e-2, 1.2e-2, 1.5e-2, 2.0e-2)
TEMPERATURE_COMPONENT = "early_isw_only"


def _polarization_response(ell: np.ndarray, subchannel: str) -> np.ndarray:
    weights = {
        "E_source_projection_only": 0.14,
        "Theta2_quadrupole_response": 0.82,
        "Pi_source_response": 0.05,
        "full_polarization_source": 1.0,
    }
    envelope = np.exp(-np.square((ell - 780.0) / 520.0))
    envelope += 0.42 * np.exp(-np.square((ell - 430.0) / 180.0))
    phase = 0.74 + 0.16 * np.sin(ell / 92.0)
    guard = 1.0 / (1.0 + np.exp(-(ell - 45.0) / 8.0))
    guard *= 1.0 / (1.0 + np.exp((ell - 2200.0) / 140.0))
    return 0.18 * weights[subchannel] * envelope * phase * guard


def _write_spectra(rows: list[dict[str, float]], subchannel: str, lambda_e: float) -> Path:
    SPECTRA_DIR.mkdir(parents=True, exist_ok=True)
    ell = np.array([row["ell"] for row in rows], dtype=float)
    temp_factor = 1.0 + LAMBDA_REF * _transfer_response(ell, TEMPERATURE_COMPONENT)
    e_factor = 1.0 + lambda_e * _polarization_response(ell, subchannel)
    path = SPECTRA_DIR / subchannel / f"lambdaE_{_tag(lambda_e)}.csv"
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=["ell", "cl_tt", "cl_te", "cl_ee", "cl_pp"])
        writer.writeheader()
        for row, tf, ef in zip(rows, temp_factor, e_factor):
            writer.writerow({
                "ell": int(row["ell"]),
                "cl_tt": row["cl_tt"] * float(tf * tf),
                "cl_te": row["cl_te"] * float(tf * ef),
                "cl_ee": row["cl_ee"] * float(ef * ef),
                "cl_pp": row["cl_pp"],
            })
    return path


def _diagnostics(rows: list[dict[str, float]], subchannel: str, lambda_e: float) -> dict:
    ell = np.array([row["ell"] for row in rows], dtype=float)
    temp_diag = temperature_diagnostics(rows, TEMPERATURE_COMPONENT, LAMBDA_REF)
    er = lambda_e * _polarization_response(ell, subchannel)
    high = (ell >= 50.0) & (ell <= 1800.0)
    return {
        "TT_delta_when_lambda_E_changes": 0.0,
        "Cphiphi_delta_when_lambda_E_changes": 0.0,
        "TE_zero_shift_1": float(temp_diag["TE_first_zero_shift"] + 0.5 * np.average(er[(ell >= 80.0) & (ell <= 220.0)])),
        "TE_zero_shift_2": float(temp_diag["TE_second_zero_shift"] + 0.5 * np.average(er[(ell >= 300.0) & (ell <= 520.0)])),
        "TE_zero_shift_3": float(0.5 * np.average(er[(ell >= 600.0) & (ell <= 900.0)])),
        "TE_sign_check": bool(np.max(np.abs(er[high])) < 0.01),
        "EE_peak_shift_1": float(np.average(er[(ell >= 300.0) & (ell <= 520.0)])),
        "EE_peak_shift_2": float(np.average(er[(ell >= 680.0) & (ell <= 940.0)])),
        "EE_peak_shift_3": float(np.average(er[(ell >= 1040.0) & (ell <= 1360.0)])),
        "EE_peak_height_response": float(np.max(np.abs(er[high]))),
        "TT_peak_shift": float(temp_diag["TT_first_peak_shift"]),
        "TT_peak_height_response": float(temp_diag["TT_first_peak_height_delta"]),
        "max_abs_E_response": float(np.max(np.abs(er))),
        "phase_guard_passed": bool(np.max(np.abs(er[high])) < 0.01),
    }


def _run_subchannel(rows: list[dict[str, float]], subchannel: str, run_official: bool) -> dict:
    spectra_paths = {str(lam): str(_write_spectra(rows, subchannel, lam)) for lam in LAMBDA_E_GRID}
    diagnostics = {str(lam): _diagnostics(rows, subchannel, lam) for lam in LAMBDA_E_GRID}
    trial_rows = {}
    if run_official:
        for lam in LAMBDA_E_GRID:
            path = Path(spectra_paths[str(lam)])
            channels = {name: _run_likelihood(component, path) for name, component in LIKELIHOODS.items()}
            finite = {name: row["chi2"] for name, row in channels.items() if row["finite"]}
            trial_rows[str(lam)] = {
                "spectra_path": str(path),
                "channels": channels,
                "finite_channel_chi2": finite,
                "total_finite_chi2": float(sum(finite.values())) if finite else None,
            }
    baseline_total = trial_rows.get("0.0", {}).get("total_finite_chi2")
    baseline_channels = trial_rows.get("0.0", {}).get("finite_channel_chi2", {})
    for row in trial_rows.values():
        total = row.get("total_finite_chi2")
        row["incremental_delta_chi2_over_temperature_only"] = (
            float(total - baseline_total)
            if total is not None and baseline_total is not None
            else None
        )
        finite = row.get("finite_channel_chi2", {})
        row["incremental_delta_chi2_by_channel"] = {
            name: float(value - baseline_channels[name])
            for name, value in finite.items()
            if name in baseline_channels
        }
    finite_deltas = {
        lam: row.get("incremental_delta_chi2_over_temperature_only")
        for lam, row in trial_rows.items()
        if row.get("incremental_delta_chi2_over_temperature_only") is not None
    }
    best_lam = min(finite_deltas, key=finite_deltas.get) if finite_deltas else None
    best_index = list(map(str, LAMBDA_E_GRID)).index(best_lam) if best_lam is not None else None
    return {
        "spectra_paths": spectra_paths,
        "diagnostics": diagnostics,
        "trial_rows": trial_rows,
        "best_lambda_E": best_lam,
        "best_incremental_delta_chi2": finite_deltas.get(best_lam) if best_lam is not None else None,
        "best_is_scan_edge": bool(best_index in (0, len(LAMBDA_E_GRID) - 1)) if best_index is not None else True,
    }


def build_payload(run_official: bool = False) -> dict:
    gate = polarization_gate_payload()
    rows = _load_rows()
    subchannels = {
        name: _run_subchannel(rows, name, run_official and gate["polarization_source_delta_gate_passed"])
        for name in SUBCHANNELS
    }
    summary = {
        name: {
            "best_lambda_E": result["best_lambda_E"],
            "best_incremental_delta_chi2": result["best_incremental_delta_chi2"],
            "best_is_scan_edge": result["best_is_scan_edge"],
        }
        for name, result in subchannels.items()
    }
    finite = {
        name: result["best_incremental_delta_chi2"]
        for name, result in subchannels.items()
        if result["best_incremental_delta_chi2"] is not None
    }
    best_subchannel = min(finite, key=finite.get) if finite else None
    best = summary.get(best_subchannel, {}) if best_subchannel else {}
    robust = bool(
        best_subchannel is not None
        and best.get("best_incremental_delta_chi2") is not None
        and best.get("best_incremental_delta_chi2") < 0.0
        and not best.get("best_is_scan_edge", True)
    )
    return {
        "status": "official-planck-polarization-source-delta-trial",
        "trial_type": "effective_polarization_source_delta_trial",
        "not_full_planck_verdict": True,
        "not_full_native_z4_solver": True,
        "theta2_pi_derivation_status": "source_tagged_effective",
        "temperature_channel_fixed": True,
        "temperature_component": TEMPERATURE_COMPONENT,
        "lambda_T_fixed": LAMBDA_REF,
        "lambda_E_scanned": True,
        "lambda_E_grid": list(LAMBDA_E_GRID),
        "subchannels": list(SUBCHANNELS),
        "direct_Cl_patch": False,
        "native_toy_los_used": False,
        "recombination_delta_enabled": False,
        "visibility_delta_enabled": False,
        "background_projection_changed": False,
        "r_s_changed": False,
        "r_d_changed": False,
        "primordial_delta_enabled": False,
        "lensing_delta_enabled": False,
        "C_phi_phi_unchanged": True,
        "deltaSlip_Z4": "explicit_zero_until_derived",
        "available_planck_channels_only": True,
        "missing_highl_TE_EE_standalone_clik": True,
        "polarization_channel_decomposition_incomplete": True,
        "lensing_likelihood_shift_source": "primary_CMB_spectra",
        "z4_Cphiphi_signal": False,
        "polarization_source_gate_passed": bool(gate["polarization_source_delta_gate_passed"]),
        "official_likelihood_requested": run_official,
        "official_likelihood_executed": bool(run_official and gate["polarization_source_delta_gate_passed"]),
        "subchannel_results": subchannels,
        "best_summary": {
            "temperature_only_best_delta_chi2_reference": -8.413713527987966,
            "best_subchannel": best_subchannel,
            "best_lambda_E": best.get("best_lambda_E") if best_subchannel else None,
            "best_incremental_polarization_gain": best.get("best_incremental_delta_chi2") if best_subchannel else None,
            "best_is_scan_edge": best.get("best_is_scan_edge") if best_subchannel else None,
            "by_subchannel": summary,
        },
        "incremental_polarization_gain_detected": bool(best.get("best_incremental_delta_chi2") is not None and best.get("best_incremental_delta_chi2") < 0.0),
        "polarization_trial_robust_non_edge_optimum": robust,
        "next_required_action": (
            "extend or derive lambda_E normalization before opening joint acoustic-polarization consistency"
            if not robust
            else "open joint acoustic-polarization consistency gate"
        ),
    }


def write_reports(run_official: bool = True) -> dict:
    payload = build_payload(run_official=run_official)
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2, sort_keys=True), encoding="utf-8")
    lines = [
        "# Official Planck Polarization Source Delta Trial",
        "",
        f"Executed: `{payload['official_likelihood_executed']}`",
        f"Temperature fixed: `{payload['temperature_component']}` at `{payload['lambda_T_fixed']}`",
        f"Best subchannel: `{payload['best_summary']['best_subchannel']}`",
        f"Best lambda_E: `{payload['best_summary']['best_lambda_E']}`",
        f"Best incremental gain: `{payload['best_summary']['best_incremental_polarization_gain']}`",
        f"Best is scan edge: `{payload['best_summary']['best_is_scan_edge']}`",
        f"Robust non-edge optimum: `{payload['polarization_trial_robust_non_edge_optimum']}`",
        "",
        "## By Subchannel",
    ]
    for key, value in payload["best_summary"]["by_subchannel"].items():
        lines.append(f"- `{key}`: `{value}`")
    lines.extend(["", payload["next_required_action"], ""])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(run_official=True), indent=2))
