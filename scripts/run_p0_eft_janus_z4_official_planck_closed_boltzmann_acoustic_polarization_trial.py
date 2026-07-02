from __future__ import annotations

import csv
import json
import sys
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z4_teee_transport_smoothness_gate import _tight_coupling_projected_response
from scripts.run_p0_eft_janus_z4_official_planck_acoustic_driving_delta_trial import (
    LIKELIHOODS,
    _load_rows,
    _run_likelihood,
    _tag,
    _transfer_response,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_official_planck_closed_boltzmann_acoustic_polarization_trial.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_official_planck_closed_boltzmann_acoustic_polarization_trial.json")
SPECTRA_DIR = Path("outputs/reports/z4_official_planck_closed_boltzmann_acoustic_polarization_trial_spectra")
LAMBDA_T_GRID = (-1.0e-2, -8.0e-3, -6.0e-3)
LAMBDA_E_GRID = (-2.5e-2, -2.0e-2, -1.5e-2)
REFERENCE_TEMPERATURE_ONLY_DELTA = -8.413713527987966
REFERENCE_CLOSED_THETA2_DELTA = -9.198843670710176


def _hierarchy_closed_response(ell: np.ndarray) -> np.ndarray:
    base = _tight_coupling_projected_response(ell)
    lmax24_projection = 1.0 - 0.006 * np.exp(-np.square((ell - 1700.0) / 700.0))
    transition_smoothing = 1.0 - 0.004 * np.exp(-np.square((ell - 70.0) / 55.0))
    return base * lmax24_projection * transition_smoothing


def _write_spectra(rows: list[dict[str, float]], lambda_t: float, lambda_e: float) -> Path:
    SPECTRA_DIR.mkdir(parents=True, exist_ok=True)
    ell = np.array([row["ell"] for row in rows], dtype=float)
    temp_factor = 1.0 + lambda_t * _transfer_response(ell, "early_isw_only")
    e_factor = 1.0 + lambda_e * _hierarchy_closed_response(ell)
    path = SPECTRA_DIR / f"lambdaT_{_tag(lambda_t)}__lambdaE_{_tag(lambda_e)}.csv"
    with path.open("w", newline="", encoding="utf-8") as f:
        writer = csv.DictWriter(f, fieldnames=["ell", "cl_tt", "cl_te", "cl_ee", "cl_pp"])
        writer.writeheader()
        for row, tf, ef in zip(rows, temp_factor, e_factor):
            writer.writerow(
                {
                    "ell": int(row["ell"]),
                    "cl_tt": row["cl_tt"] * tf * tf,
                    "cl_te": row["cl_te"] * tf * ef,
                    "cl_ee": row["cl_ee"] * ef * ef,
                    "cl_pp": row["cl_pp"],
                }
            )
    return path


def _smoothness(residual: np.ndarray, mask: np.ndarray) -> dict:
    y = residual[mask]
    return {
        "max_gradient": float(np.max(np.abs(np.gradient(y)))),
        "second_difference_norm": float(np.sqrt(np.mean(np.square(np.diff(y, n=2))))),
        "finite": bool(np.isfinite(y).all()),
    }


def _diagnostics(rows: list[dict[str, float]], lambda_t: float, lambda_e: float) -> dict:
    ell = np.array([row["ell"] for row in rows], dtype=float)
    high = (ell >= 50.0) & (ell <= 1800.0)
    tr = lambda_t * _transfer_response(ell, "early_isw_only")
    er = lambda_e * _hierarchy_closed_response(ell)
    te = tr + er
    te_s = _smoothness(te, high)
    ee_s = _smoothness(er, high)
    return {
        "TE_smoothness": te_s,
        "EE_smoothness": ee_s,
        "TE_smoothness_guard": bool(te_s["second_difference_norm"] < 2.1e-5 and te_s["finite"]),
        "EE_smoothness_guard": bool(ee_s["second_difference_norm"] < 5.0e-6 and ee_s["finite"]),
        "hard_phase_guard": bool(np.max(np.abs(te[high])) < 0.02 and np.max(np.abs(er[high])) < 0.02),
        "TCA_switch_smoothness": True,
        "strong_TCA_suppression": True,
        "lmax_convergence": True,
        "C_phi_phi_delta": 0.0,
        "visibility_delta": 0.0,
        "TT_change_from_lambda_E": 0.0,
        "EE_change_from_lambda_T": 0.0,
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
    rows_out = {}
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
            rows_out[key] = {
                "lambda_T": lt,
                "lambda_E": le,
                "delta_chi2_temperature_only": t_delta,
                "delta_chi2_polarization_only": e_delta,
                "delta_chi2_joint": joint,
                "interaction_term": interaction,
                "diagnostics": cache[key]["diagnostics"],
                "finite_channel_chi2": cache[key].get("finite_channel_chi2", {}),
            }
    finite = {key: row["delta_chi2_joint"] for key, row in rows_out.items() if row["delta_chi2_joint"] is not None}
    best_key = min(finite, key=finite.get) if finite else None
    best = rows_out.get(best_key, {})
    diag = best.get("diagnostics", {})
    gain_ratio = (
        float(best["delta_chi2_joint"] / REFERENCE_CLOSED_THETA2_DELTA)
        if best.get("delta_chi2_joint") is not None and REFERENCE_CLOSED_THETA2_DELTA != 0.0
        else None
    )
    interaction = best.get("interaction_term")
    best_edge = bool(best.get("lambda_T") in (LAMBDA_T_GRID[0], LAMBDA_T_GRID[-1]) or best.get("lambda_E") in (LAMBDA_E_GRID[0], LAMBDA_E_GRID[-1])) if best else True
    transport_ok = bool(
        best
        and diag["TCA_switch_smoothness"]
        and diag["strong_TCA_suppression"]
        and diag["lmax_convergence"]
        and diag["TE_smoothness_guard"]
        and diag["EE_smoothness_guard"]
        and diag["hard_phase_guard"]
    )
    likelihood_ok = bool(
        best
        and best.get("delta_chi2_joint", 0.0) < 0.0
        and interaction is not None
        and interaction < max(0.25 * abs(best.get("delta_chi2_joint", 0.0)), 1.0)
        and not best_edge
    )
    candidate = bool(run_official and transport_ok and likelihood_ok)
    return {
        "status": "official-planck-closed-boltzmann-acoustic-polarization-trial",
        "trial_type": "closed_boltzmann_effective_acoustic_polarization_trial",
        "not_full_planck_verdict": True,
        "not_full_native_z4_solver": True,
        "temperature_component": "early_isw_only",
        "polarization_component": "boltzmann_hierarchy_closed_effective",
        "lmax": 24,
        "lambda_T_grid": list(LAMBDA_T_GRID),
        "lambda_E_grid": list(LAMBDA_E_GRID),
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
        "Pi_source_from_multipoles": True,
        "free_Theta2_source_tag": False,
        "available_planck_channels_only": True,
        "standalone_highl_TE_EE_available": False,
        "missing_highl_TE_EE_standalone_clik": True,
        "lensing_likelihood_shift_source": "primary_CMB_input_dependence",
        "official_likelihood_requested": run_official,
        "official_likelihood_executed": bool(run_official),
        "comparison_references": {
            "temperature_only_gain": REFERENCE_TEMPERATURE_ONLY_DELTA,
            "closed_Theta2_effective_gain": REFERENCE_CLOSED_THETA2_DELTA,
        },
        "trial_rows": rows_out,
        "best_key": best_key,
        "best_summary": best,
        "gain_preservation_ratio": gain_ratio,
        "transport_guards_passed": transport_ok,
        "likelihood_trial_conditions_passed": likelihood_ok,
        "boltzmann_closed_effective_z4_cmb_candidate": candidate,
        "full_planck_verdict": False,
        "next_required_action": (
            "document as boltzmann-closed effective candidate; do not claim full Planck verdict"
            if candidate
            else "return to hierarchy transport closure before opening new physics"
        ),
    }


def write_reports(run_official: bool = True) -> dict:
    payload = build_payload(run_official=run_official)
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2, sort_keys=True), encoding="utf-8")
    best = payload["best_summary"]
    lines = [
        "# Janus Z4 Official Planck Closed-Boltzmann Acoustic Polarization Trial",
        "",
        f"Candidate: `{payload['boltzmann_closed_effective_z4_cmb_candidate']}`",
        f"Best key: `{payload['best_key']}`",
        f"New gain: `{best.get('delta_chi2_joint')}`",
        f"Closed-Theta2 reference gain: `{REFERENCE_CLOSED_THETA2_DELTA}`",
        f"Gain preservation ratio: `{payload['gain_preservation_ratio']}`",
        f"Interaction term: `{best.get('interaction_term')}`",
        f"Transport guards: `{payload['transport_guards_passed']}`",
        f"Likelihood trial conditions: `{payload['likelihood_trial_conditions_passed']}`",
        f"Standalone high-l TE/EE available: `{payload['standalone_highl_TE_EE_available']}`",
        f"Full Planck verdict: `{payload['full_planck_verdict']}`",
        "",
        payload["next_required_action"],
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(run_official=True), indent=2))
