from __future__ import annotations

import csv
import json
import sys
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z4_acoustic_driving_delta_gate import (
    _acoustic_source,
    build_payload as acoustic_gate_payload,
)
from scripts.build_p0_eft_janus_z4_camb_gr_baseline_export import SPECTRA_PATH as CAMB_GR_PATH
from scripts.build_p0_eft_janus_z4_camb_gr_baseline_export import write_reports as write_camb_gr
from scripts.build_p0_eft_janus_z4_weyl_late_isw_consistency_gate import _grid
from scripts.run_p0_eft_janus_z4_official_planck_lensing_shape_delta_trial import (
    LIKELIHOODS,
    _run_likelihood,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_official_planck_acoustic_driving_delta_trial.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_official_planck_acoustic_driving_delta_trial.json")
SPECTRA_DIR = Path("outputs/reports/z4_acoustic_driving_delta_trial_spectra")
LAMBDAS = (-1.0e-2, -3.0e-3, -1.0e-3, 0.0, 1.0e-3, 3.0e-3, 1.0e-2)
COMPONENTS = ("surface_only", "early_isw_only", "full")


def _load_rows() -> list[dict[str, float]]:
    if not CAMB_GR_PATH.exists():
        write_camb_gr()
    with CAMB_GR_PATH.open(encoding="utf-8") as handle:
        rows = [{key: float(value) for key, value in row.items()} for row in csv.DictReader(handle)]
    if not rows or rows[-1]["ell"] < 2508:
        write_camb_gr()
        with CAMB_GR_PATH.open(encoding="utf-8") as handle:
            rows = [{key: float(value) for key, value in row.items()} for row in csv.DictReader(handle)]
    return rows


def _tag(value: float) -> str:
    if value == 0.0:
        return "p0"
    sign = "m" if value < 0 else "p"
    return f"{sign}{abs(value):.0e}".replace("+", "").replace("-", "").replace(".", "p")


def _source_amplitudes() -> dict[str, float]:
    k, tau = _grid()
    source = _acoustic_source(k, tau)
    surface = float(np.sqrt(np.mean(np.square(source["sw_surface_component"]))))
    eisw = float(np.sqrt(np.mean(np.square(source["early_isw_component"]))))
    total = surface + eisw
    return {
        "surface_only": surface / max(total, 1.0e-300),
        "early_isw_only": eisw / max(total, 1.0e-300),
        "full": 1.0,
    }


def _transfer_response(ell: np.ndarray, component: str) -> np.ndarray:
    amps = _source_amplitudes()
    acoustic_envelope = np.exp(-np.square((ell - 820.0) / 520.0))
    acoustic_envelope += 0.55 * np.exp(-np.square((ell - 215.0) / 105.0))
    acoustic_phase = 0.72 + 0.18 * np.cos(ell / 74.0)
    low_l_guard = 1.0 / (1.0 + np.exp(-(ell - 35.0) / 6.0))
    high_l_guard = 1.0 / (1.0 + np.exp((ell - 2100.0) / 120.0))
    response = 0.32 * amps[component] * acoustic_envelope * acoustic_phase * low_l_guard * high_l_guard
    return response


def _write_spectra(rows: list[dict[str, float]], component: str, lam: float) -> Path:
    SPECTRA_DIR.mkdir(parents=True, exist_ok=True)
    ell = np.array([row["ell"] for row in rows], dtype=float)
    transfer_factor = 1.0 + lam * _transfer_response(ell, component)
    path = SPECTRA_DIR / component / f"lambda_{_tag(lam)}.csv"
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=["ell", "cl_tt", "cl_te", "cl_ee", "cl_pp"])
        writer.writeheader()
        for row, tf in zip(rows, transfer_factor):
            writer.writerow({
                "ell": int(row["ell"]),
                "cl_tt": row["cl_tt"] * float(tf * tf),
                "cl_te": row["cl_te"] * float(tf),
                "cl_ee": row["cl_ee"],
                "cl_pp": row["cl_pp"],
            })
    return path


def _diagnostics(rows: list[dict[str, float]], component: str, lam: float) -> dict:
    ell = np.array([row["ell"] for row in rows], dtype=float)
    response = lam * _transfer_response(ell, component)
    peak_windows = {
        "first": (ell >= 160.0) & (ell <= 260.0),
        "second": (ell >= 470.0) & (ell <= 620.0),
        "third": (ell >= 720.0) & (ell <= 910.0),
    }
    high = (ell >= 50.0) & (ell <= 1800.0)
    return {
        "TT_first_peak_shift": float(np.average(response[peak_windows["first"]])),
        "TT_first_peak_height_delta": float(np.max(response[peak_windows["first"]])),
        "TT_second_peak_height_delta": float(np.max(response[peak_windows["second"]])),
        "TT_third_peak_height_delta": float(np.max(response[peak_windows["third"]])),
        "TE_first_zero_shift": float(0.5 * np.average(response[(ell >= 80.0) & (ell <= 220.0)])),
        "TE_second_zero_shift": float(0.5 * np.average(response[(ell >= 300.0) & (ell <= 520.0)])),
        "TE_sign_check": bool(np.max(np.abs(response[high])) < 0.01),
        "EE_max_delta": 0.0,
        "Cphiphi_max_delta": 0.0,
        "max_abs_transfer_response": float(np.max(np.abs(response))),
    }


def _run_component(rows: list[dict[str, float]], component: str, run_official: bool) -> dict:
    spectra_paths = {str(lam): str(_write_spectra(rows, component, lam)) for lam in LAMBDAS}
    diagnostics = {str(lam): _diagnostics(rows, component, lam) for lam in LAMBDAS}
    trial_rows = {}
    if run_official:
        for lam in LAMBDAS:
            path = Path(spectra_paths[str(lam)])
            channels = {name: _run_likelihood(likelihood, path) for name, likelihood in LIKELIHOODS.items()}
            finite = {name: row["chi2"] for name, row in channels.items() if row["finite"]}
            trial_rows[str(lam)] = {
                "spectra_path": str(path),
                "channels": channels,
                "finite_channel_chi2": finite,
                "total_finite_chi2": float(sum(finite.values())) if finite else None,
            }
    baseline_total = trial_rows.get("0.0", {}).get("total_finite_chi2")
    for row in trial_rows.values():
        total = row.get("total_finite_chi2")
        row["delta_chi2_total_available"] = (
            float(total - baseline_total)
            if total is not None and baseline_total is not None
            else None
        )
        finite = row.get("finite_channel_chi2", {})
        baseline = trial_rows.get("0.0", {}).get("finite_channel_chi2", {})
        row["delta_chi2_by_channel_available"] = {
            name: float(value - baseline[name])
            for name, value in finite.items()
            if name in baseline
        }
    finite_deltas = {
        lam: row.get("delta_chi2_total_available")
        for lam, row in trial_rows.items()
        if row.get("delta_chi2_total_available") is not None
    }
    best_lam = min(finite_deltas, key=finite_deltas.get) if finite_deltas else None
    return {
        "spectra_paths": spectra_paths,
        "diagnostics": diagnostics,
        "trial_rows": trial_rows,
        "best_lambda": best_lam,
        "best_delta_chi2": finite_deltas.get(best_lam) if best_lam is not None else None,
    }


def build_payload(run_official: bool = False) -> dict:
    gate = acoustic_gate_payload()
    rows = _load_rows()
    components = {
        component: _run_component(rows, component, run_official and gate["official_planck_acoustic_driving_trial_allowed"])
        for component in COMPONENTS
    }
    bests = {
        component: {
            "best_lambda": result["best_lambda"],
            "best_delta_chi2": result["best_delta_chi2"],
        }
        for component, result in components.items()
    }
    full_best = bests["full"]["best_delta_chi2"]
    surface_best = bests["surface_only"]["best_delta_chi2"]
    eisw_best = bests["early_isw_only"]["best_delta_chi2"]
    cancellation = (
        full_best is not None
        and surface_best is not None
        and eisw_best is not None
        and abs(full_best) < 0.5 * max(abs(surface_best), abs(eisw_best), 1.0e-300)
    )
    return {
        "status": "official-planck-acoustic-driving-delta-trial",
        "is_planck_success_verdict": False,
        "trial_type": "effective_acoustic_temperature_source_delta",
        "not_full_z4_verdict": True,
        "backend": "camb_gr_plus_z4_delta",
        "acoustic_gate_passed": bool(gate["acoustic_driving_delta_gate_passed"]),
        "delta_channels_enabled": ["acoustic_temperature_source"],
        "component_trials": list(COMPONENTS),
        "lambda_grid": list(LAMBDAS),
        "metric_split_used": True,
        "deltaSlip_Z4": "explicit_zero_until_derived",
        "polarization_source_delta_enabled": False,
        "EE_expected_unchanged": True,
        "lensing_delta_enabled": False,
        "C_phi_phi_expected_unchanged": True,
        "recombination_delta_enabled": False,
        "visibility_delta_enabled": False,
        "background_projection_changed": False,
        "primordial_delta_enabled": False,
        "native_toy_los_used": False,
        "full_native_z4_solver_used": False,
        "official_likelihood_requested": run_official,
        "official_likelihood_executed": bool(run_official and gate["official_planck_acoustic_driving_trial_allowed"]),
        "components": components,
        "best_summary": {
            "best_lambda_surface_only": bests["surface_only"]["best_lambda"],
            "best_delta_chi2_surface_only": bests["surface_only"]["best_delta_chi2"],
            "best_lambda_early_isw_only": bests["early_isw_only"]["best_lambda"],
            "best_delta_chi2_early_isw_only": bests["early_isw_only"]["best_delta_chi2"],
            "best_lambda_full": bests["full"]["best_lambda"],
            "best_delta_chi2_full": bests["full"]["best_delta_chi2"],
            "surface_eisw_cancellation_detected": bool(cancellation),
        },
        "next_required_action": "interpret surface/eISW/full channel response; do not treat as full Z4 Planck verdict",
    }


def write_reports(run_official: bool = True) -> dict:
    payload = build_payload(run_official=run_official)
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2, sort_keys=True), encoding="utf-8")
    lines = [
        "# Official Planck Acoustic Driving Delta Trial",
        "",
        f"Acoustic gate passed: `{payload['acoustic_gate_passed']}`",
        f"Planck success verdict: `{payload['is_planck_success_verdict']}`",
        f"Official likelihood executed: `{payload['official_likelihood_executed']}`",
        f"Trial type: `{payload['trial_type']}`",
        "",
        "## Best Summary",
    ]
    for key, value in payload["best_summary"].items():
        lines.append(f"- `{key}`: `{value}`")
    lines.extend(["", payload["next_required_action"], ""])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(run_official=True), indent=2))
