from __future__ import annotations

import csv
import json
import sys
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.run_p0_eft_janus_z4_official_planck_acoustic_driving_delta_trial import (
    LIKELIHOODS,
    _load_rows,
    _run_likelihood,
    _tag,
    _transfer_response,
)
from scripts.run_p0_eft_janus_z4_official_planck_polarization_source_delta_trial import (
    _polarization_response,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_acoustic_polarization_joint_consistency_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_acoustic_polarization_joint_consistency_gate.json")
SPECTRA_DIR = Path("outputs/reports/z4_acoustic_polarization_joint_consistency_gate_spectra")
TEMPERATURE_COMPONENT = "early_isw_only"
POLARIZATION_COMPONENT = "Theta2_quadrupole_response"
LAMBDA_T_GRID = (-1.2e-2, -1.0e-2, -8.0e-3, -6.0e-3, -4.0e-3)
LAMBDA_E_GRID = (-3.0e-2, -2.5e-2, -2.0e-2, -1.5e-2, -1.0e-2)


def _write_spectra(rows: list[dict[str, float]], lambda_t: float, lambda_e: float) -> Path:
    SPECTRA_DIR.mkdir(parents=True, exist_ok=True)
    ell = np.array([row["ell"] for row in rows], dtype=float)
    temp_factor = 1.0 + lambda_t * _transfer_response(ell, TEMPERATURE_COMPONENT)
    e_factor = 1.0 + lambda_e * _polarization_response(ell, POLARIZATION_COMPONENT)
    path = SPECTRA_DIR / f"lambdaT_{_tag(lambda_t)}__lambdaE_{_tag(lambda_e)}.csv"
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


def _diagnostics(rows: list[dict[str, float]], lambda_t: float, lambda_e: float) -> dict:
    ell = np.array([row["ell"] for row in rows], dtype=float)
    tr = lambda_t * _transfer_response(ell, TEMPERATURE_COMPONENT)
    er = lambda_e * _polarization_response(ell, POLARIZATION_COMPONENT)
    high = (ell >= 50.0) & (ell <= 1800.0)
    te1 = 0.5 * np.average(tr[(ell >= 80.0) & (ell <= 220.0)] + er[(ell >= 80.0) & (ell <= 220.0)])
    te2 = 0.5 * np.average(tr[(ell >= 300.0) & (ell <= 520.0)] + er[(ell >= 300.0) & (ell <= 520.0)])
    te3 = 0.5 * np.average(er[(ell >= 600.0) & (ell <= 900.0)])
    ee1 = np.average(er[(ell >= 300.0) & (ell <= 520.0)])
    ee2 = np.average(er[(ell >= 680.0) & (ell <= 940.0)])
    ee3 = np.average(er[(ell >= 1040.0) & (ell <= 1360.0)])
    return {
        "TE_zero_shift_1": float(te1),
        "TE_zero_shift_2": float(te2),
        "TE_zero_shift_3": float(te3),
        "TE_sign_guard": bool(np.max(np.abs(tr[high] + er[high])) < 0.02),
        "TE_residual_smoothness": bool(np.max(np.abs(np.gradient(tr[high] + er[high]))) < 5.0e-5),
        "EE_peak_shift_1": float(ee1),
        "EE_peak_shift_2": float(ee2),
        "EE_peak_shift_3": float(ee3),
        "EE_peak_height_response": float(np.max(np.abs(er[high]))),
        "EE_highl_residual_smoothness": bool(np.max(np.abs(np.gradient(er[high]))) < 5.0e-5),
        "C_phi_phi_delta": 0.0,
        "visibility_delta": 0.0,
        "TT_change_from_lambda_E": 0.0,
        "EE_change_from_lambda_T": 0.0,
        "phase_guard_passed": bool(
            abs(te1) < 0.02
            and abs(te2) < 0.02
            and abs(te3) < 0.02
            and abs(ee1) < 0.02
            and abs(ee2) < 0.02
            and abs(ee3) < 0.02
        ),
    }


def _run_likelihood_set(path: Path, run_official: bool) -> dict:
    if not run_official:
        return {}
    channels = {name: _run_likelihood(component, path) for name, component in LIKELIHOODS.items()}
    finite = {name: row["chi2"] for name, row in channels.items() if row["finite"]}
    return {
        "channels": channels,
        "finite_channel_chi2": finite,
        "total_finite_chi2": float(sum(finite.values())) if finite else None,
    }


def _delta(row: dict, baseline: dict) -> float | None:
    total = row.get("total_finite_chi2")
    base = baseline.get("total_finite_chi2")
    return float(total - base) if total is not None and base is not None else None


def build_payload(run_official: bool = False) -> dict:
    rows = _load_rows()
    t_values = (0.0, *LAMBDA_T_GRID)
    e_values = (0.0, *LAMBDA_E_GRID)
    cache: dict[str, dict] = {}
    for lt in t_values:
        for le in e_values:
            key = f"{lt},{le}"
            path = _write_spectra(rows, lt, le)
            cache[key] = {
                "spectra_path": str(path),
                "diagnostics": _diagnostics(rows, lt, le),
                **_run_likelihood_set(path, run_official),
            }
    baseline = cache["0.0,0.0"]
    joint_rows = {}
    for lt in LAMBDA_T_GRID:
        for le in LAMBDA_E_GRID:
            key = f"{lt},{le}"
            t_key = f"{lt},0.0"
            e_key = f"0.0,{le}"
            joint = _delta(cache[key], baseline)
            t_delta = _delta(cache[t_key], baseline)
            e_delta = _delta(cache[e_key], baseline)
            interaction = (
                float(joint - t_delta - e_delta)
                if joint is not None and t_delta is not None and e_delta is not None
                else None
            )
            joint_rows[key] = {
                "lambda_T": lt,
                "lambda_E": le,
                "delta_chi2_temperature_only": t_delta,
                "delta_chi2_polarization_only": e_delta,
                "delta_chi2_joint": joint,
                "interaction_term": interaction,
                "diagnostics": cache[key]["diagnostics"],
                "finite_channel_chi2": cache[key].get("finite_channel_chi2", {}),
            }
    finite = {key: row["delta_chi2_joint"] for key, row in joint_rows.items() if row["delta_chi2_joint"] is not None}
    best_key = min(finite, key=finite.get) if finite else None
    best = joint_rows.get(best_key, {})
    interaction = best.get("interaction_term")
    guards_ok = bool(
        best
        and best["diagnostics"]["phase_guard_passed"]
        and best["diagnostics"]["TE_sign_guard"]
        and best["diagnostics"]["TE_residual_smoothness"]
        and best["diagnostics"]["EE_highl_residual_smoothness"]
        and best["diagnostics"]["C_phi_phi_delta"] == 0.0
        and best["diagnostics"]["visibility_delta"] == 0.0
        and best["diagnostics"]["TT_change_from_lambda_E"] == 0.0
        and best["diagnostics"]["EE_change_from_lambda_T"] == 0.0
    )
    interaction_small = bool(interaction is not None and abs(interaction) < 0.25 * max(abs(best.get("delta_chi2_joint", 0.0)), 1.0e-300))
    hard_phase_guard = bool(best and best["diagnostics"]["phase_guard_passed"])
    gate = bool(run_official and best and guards_ok and interaction_small)
    return {
        "status": "janus-z4-acoustic-polarization-joint-consistency-gate",
        "temperature_component": TEMPERATURE_COMPONENT,
        "polarization_component": POLARIZATION_COMPONENT,
        "lambda_T_grid": list(LAMBDA_T_GRID),
        "lambda_E_grid": list(LAMBDA_E_GRID),
        "large_lambda_E_scan_is_diagnostic_only": True,
        "physical_interpretation_region": "local_bracket_around_minus_0p02",
        "theta2_closure_status": "source_tagged_effective",
        "boltzmann_theta2_closure_complete": False,
        "direct_Cl_patch": False,
        "native_toy_los_used": False,
        "recombination_delta_enabled": False,
        "visibility_delta_enabled": False,
        "background_projection_changed": False,
        "r_s_changed": False,
        "r_d_changed": False,
        "primordial_delta_enabled": False,
        "lensing_C_phi_phi_frozen": True,
        "slip_frozen": True,
        "available_planck_channels_only": True,
        "missing_highl_TE_EE_standalone_clik": True,
        "official_likelihood_requested": run_official,
        "official_likelihood_executed": bool(run_official),
        "baseline": baseline,
        "joint_rows": joint_rows,
        "best_key": best_key,
        "best_summary": best,
        "interaction_term_small": interaction_small,
        "hard_phase_guard_passed": hard_phase_guard,
        "joint_phase_guards_passed": guards_ok,
        "acoustic_polarization_joint_consistency_gate_passed": gate,
        "next_required_action": (
            "derive Theta2QuadrupoleClosureGate before promoting beyond effective source model"
            if gate
            else "do not promote joint source; derive Theta2 closure and TE/EE transport smoothness"
        ),
    }


def write_reports(run_official: bool = True) -> dict:
    payload = build_payload(run_official=run_official)
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2, sort_keys=True), encoding="utf-8")
    best = payload["best_summary"]
    lines = [
        "# Janus Z4 Acoustic Polarization Joint Consistency Gate",
        "",
        f"Gate passed: `{payload['acoustic_polarization_joint_consistency_gate_passed']}`",
        f"Best key: `{payload['best_key']}`",
        f"Best joint delta chi2: `{best.get('delta_chi2_joint')}`",
        f"Temperature delta: `{best.get('delta_chi2_temperature_only')}`",
        f"Polarization delta: `{best.get('delta_chi2_polarization_only')}`",
        f"Interaction term: `{best.get('interaction_term')}`",
        f"Hard phase guard: `{payload['hard_phase_guard_passed']}`",
        f"All joint guards: `{payload['joint_phase_guards_passed']}`",
        "",
        payload["next_required_action"],
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(run_official=True), indent=2))
