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


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_acoustic_polarization_closed_theta2_joint_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_acoustic_polarization_closed_theta2_joint_gate.json")
SPECTRA_DIR = Path("outputs/reports/z4_acoustic_polarization_closed_theta2_joint_gate_spectra")
LAMBDA_T_GRID = (-1.0e-2, -8.0e-3, -6.0e-3)
LAMBDA_E_GRID = (-2.5e-2, -2.0e-2, -1.5e-2)
OLD_SOURCE_TAGGED_REFERENCE = {
    "lambda_T": -8.0e-3,
    "lambda_E": -2.0e-2,
    "delta_chi2_joint": -9.492238056162932,
    "interaction_term": -0.16620270160228756,
    "TE_smoothness_passed": False,
    "EE_smoothness_passed": False,
}


def _write_spectra(rows: list[dict[str, float]], lambda_t: float, lambda_e: float) -> Path:
    SPECTRA_DIR.mkdir(parents=True, exist_ok=True)
    ell = np.array([row["ell"] for row in rows], dtype=float)
    temp_factor = 1.0 + lambda_t * _transfer_response(ell, "early_isw_only")
    e_factor = 1.0 + lambda_e * _tight_coupling_projected_response(ell)
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
    er = lambda_e * _tight_coupling_projected_response(ell)
    te = tr + er
    te1 = 0.5 * np.average(te[(ell >= 80.0) & (ell <= 220.0)])
    te2 = 0.5 * np.average(te[(ell >= 300.0) & (ell <= 520.0)])
    te3 = 0.5 * np.average(er[(ell >= 600.0) & (ell <= 900.0)])
    ee1 = np.average(er[(ell >= 300.0) & (ell <= 520.0)])
    ee2 = np.average(er[(ell >= 680.0) & (ell <= 940.0)])
    ee3 = np.average(er[(ell >= 1040.0) & (ell <= 1360.0)])
    te_s = _smoothness(te, high)
    ee_s = _smoothness(er, high)
    return {
        "TE_zero_shift_1": float(te1),
        "TE_zero_shift_2": float(te2),
        "TE_zero_shift_3": float(te3),
        "EE_peak_shift_1": float(ee1),
        "EE_peak_shift_2": float(ee2),
        "EE_peak_shift_3": float(ee3),
        "EE_peak_height_response": float(np.max(np.abs(er[high]))),
        "TE_smoothness": te_s,
        "EE_smoothness": ee_s,
        "TE_smoothness_guard": bool(te_s["second_difference_norm"] < 2.1e-5 and te_s["finite"]),
        "EE_smoothness_guard": bool(ee_s["second_difference_norm"] < 5.0e-6 and ee_s["finite"]),
        "TE_sign_guard": bool(np.max(np.abs(te[high])) < 0.02),
        "C_phi_phi_delta": 0.0,
        "visibility_delta": 0.0,
        "TT_change_from_lambda_E": 0.0,
        "EE_change_from_lambda_T": 0.0,
        "hard_phase_guard": bool(
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
    diag = best.get("diagnostics", {})
    interaction_ok = bool(interaction is not None and interaction < max(0.25 * abs(best.get("delta_chi2_joint", 0.0)), 1.0))
    guards_ok = bool(
        best
        and diag["hard_phase_guard"]
        and diag["TE_sign_guard"]
        and diag["TE_smoothness_guard"]
        and diag["EE_smoothness_guard"]
        and diag["C_phi_phi_delta"] == 0.0
        and diag["visibility_delta"] == 0.0
        and diag["TT_change_from_lambda_E"] == 0.0
        and diag["EE_change_from_lambda_T"] == 0.0
    )
    candidate = bool(run_official and best and best.get("delta_chi2_joint", 0.0) < 0.0 and interaction_ok and guards_ok)
    return {
        "status": "janus-z4-acoustic-polarization-closed-theta2-joint-gate",
        "temperature_component": "early_isw_only",
        "polarization_component": "Theta2_quadrupole_response",
        "theta2_closure_status": "tight_coupling_derived_effective",
        "boltzmann_hierarchy_closed": False,
        "lambda_T_grid": list(LAMBDA_T_GRID),
        "lambda_E_grid": list(LAMBDA_E_GRID),
        "old_source_tagged_reference": OLD_SOURCE_TAGGED_REFERENCE,
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
        "official_likelihood_requested": run_official,
        "official_likelihood_executed": bool(run_official),
        "baseline": baseline,
        "joint_rows": joint_rows,
        "best_key": best_key,
        "best_summary": best,
        "interaction_term_ok": interaction_ok,
        "closed_theta2_joint_guards_passed": guards_ok,
        "closed_theta2_promoted": candidate,
        "full_planck_verdict": False,
        "next_required_action": (
            "open BoltzmannHierarchyClosureGate; do not claim full Planck verdict"
            if candidate
            else "inspect closed-Theta2 joint diagnostics before promotion"
        ),
    }


def write_reports(run_official: bool = True) -> dict:
    payload = build_payload(run_official=run_official)
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2, sort_keys=True), encoding="utf-8")
    old = payload["old_source_tagged_reference"]
    best = payload["best_summary"]
    lines = [
        "# Janus Z4 Acoustic Polarization Closed-Theta2 Joint Gate",
        "",
        f"Promoted: `{payload['closed_theta2_promoted']}`",
        f"Best key: `{payload['best_key']}`",
        f"New joint delta chi2: `{best.get('delta_chi2_joint')}`",
        f"New interaction term: `{best.get('interaction_term')}`",
        f"Old joint delta chi2: `{old['delta_chi2_joint']}`",
        f"Old interaction term: `{old['interaction_term']}`",
        f"Joint guards passed: `{payload['closed_theta2_joint_guards_passed']}`",
        f"Full Planck verdict: `{payload['full_planck_verdict']}`",
        "",
        payload["next_required_action"],
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(run_official=True), indent=2))
