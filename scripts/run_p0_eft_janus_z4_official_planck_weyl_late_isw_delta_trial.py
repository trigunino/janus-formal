from __future__ import annotations

import csv
import json
import sys
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z4_camb_gr_baseline_export import SPECTRA_PATH as CAMB_GR_PATH
from scripts.build_p0_eft_janus_z4_camb_gr_baseline_export import write_reports as write_camb_gr
from scripts.build_p0_eft_janus_z4_weyl_late_isw_consistency_gate import (
    _grid,
    _late_isw_from_shared_weyl,
    _lensing_kernel_from_shared_weyl,
    build_payload as consistency_payload,
)
from scripts.run_p0_eft_janus_z4_official_planck_lensing_shape_delta_trial import (
    LAMBDAS,
    LIKELIHOODS,
    _run_likelihood,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_official_planck_weyl_late_isw_delta_trial.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_official_planck_weyl_late_isw_delta_trial.json")
SPECTRA_DIR = Path("outputs/reports/z4_weyl_late_isw_delta_trial_spectra")


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


def _shared_projection(ell: np.ndarray) -> tuple[np.ndarray, np.ndarray]:
    k, tau = _grid()
    x_z4, _, source = _late_isw_from_shared_weyl(k, tau)
    lens_kernel = _lensing_kernel_from_shared_weyl(k, tau, x_z4)
    lens_scalar = float(np.trapezoid(np.trapezoid(lens_kernel, tau, axis=1), np.log(k)))
    isw_scalar = float(np.trapezoid(np.trapezoid(source, tau, axis=1), np.log(k)))
    low_l_window = np.exp(-np.square((ell - 18.0) / 22.0))
    low_l_window *= 1.0 / (1.0 + np.exp((ell - 75.0) / 5.0))
    phiphi_window = np.square(ell / 80.0) / (1.0 + np.square(ell / 80.0))
    phiphi_window *= 1.0 / (1.0 + np.square(ell / 700.0))
    tt_response = 2.0e-3 * isw_scalar * low_l_window
    phiphi_response = 2.0e-3 * lens_scalar * phiphi_window
    return tt_response, phiphi_response


def _write_spectra(rows: list[dict[str, float]], lam: float) -> Path:
    SPECTRA_DIR.mkdir(parents=True, exist_ok=True)
    ell = np.array([row["ell"] for row in rows], dtype=float)
    tt_response, pp_response = _shared_projection(ell)
    path = SPECTRA_DIR / f"lambda_{_tag(lam)}.csv"
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=["ell", "cl_tt", "cl_te", "cl_ee", "cl_pp"])
        writer.writeheader()
        for row, dtt, dpp in zip(rows, tt_response, pp_response):
            writer.writerow({
                "ell": int(row["ell"]),
                "cl_tt": row["cl_tt"] * (1.0 + lam * float(dtt)),
                "cl_te": row["cl_te"],
                "cl_ee": row["cl_ee"],
                "cl_pp": row["cl_pp"] * (1.0 + lam * float(dpp)),
            })
    return path


def _response_stats(rows: list[dict[str, float]]) -> dict:
    ell = np.array([row["ell"] for row in rows], dtype=float)
    tt_response, pp_response = _shared_projection(ell)
    high_mask = (ell >= 100.0) & (ell <= 1200.0)
    low_mask = (ell >= 2.0) & (ell <= 80.0)
    return {
        "max_abs_low_l_TT_response_per_lambda": float(np.max(np.abs(tt_response[low_mask]))),
        "max_abs_high_l_TT_response_per_lambda": float(np.max(np.abs(tt_response[high_mask]))),
        "max_abs_phiphi_response_per_lambda": float(np.max(np.abs(pp_response[ell >= 8.0]))),
        "high_l_TT_is_frozen": bool(np.max(np.abs(tt_response[high_mask])) < 1.0e-8),
        "TE_EE_frozen_by_construction": True,
    }


def build_payload(run_official: bool = False) -> dict:
    consistency = consistency_payload()
    rows = _load_rows()
    spectra_paths = {str(lam): str(_write_spectra(rows, lam)) for lam in LAMBDAS}
    trial_rows = {}
    if run_official and consistency["official_planck_weyl_late_isw_trial_allowed"]:
        for lam in LAMBDAS:
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
    for row in trial_rows.values():
        total = row.get("total_finite_chi2")
        row["delta_chi2_total_available"] = (
            float(total - baseline_total)
            if total is not None and baseline_total is not None
            else None
        )
    return {
        "status": "official-planck-weyl-late-isw-delta-trial",
        "is_planck_success_verdict": False,
        "consistency_gate_passed": bool(consistency["weyl_late_isw_consistency_gate_passed"]),
        "backend": "camb_gr_plus_z4_delta",
        "delta_channels_enabled": ["shared_weyl_lensing", "late_isw_source"],
        "early_isw_enabled": False,
        "acoustic_delta_enabled": False,
        "recombination_delta_enabled": False,
        "polarization_delta_enabled": False,
        "native_toy_los_used": False,
        "full_native_z4_solver_used": False,
        "trial_type": "effective_shared_weyl_late_isw",
        "lambda_grid": list(LAMBDAS),
        "response_stats": _response_stats(rows),
        "spectra_paths": spectra_paths,
        "official_likelihood_requested": run_official,
        "official_likelihood_executed": bool(trial_rows),
        "trial_rows": trial_rows,
        "next_required_action": "inspect low-l TT and lensing deltas; this remains an effective trial, not a full Z4 verdict",
    }


def write_reports(run_official: bool = True) -> dict:
    payload = build_payload(run_official=run_official)
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2, sort_keys=True), encoding="utf-8")
    lines = [
        "# Official Planck Weyl Late-ISW Delta Trial",
        "",
        f"Consistency gate passed: `{payload['consistency_gate_passed']}`",
        f"Planck success verdict: `{payload['is_planck_success_verdict']}`",
        f"Official likelihood executed: `{payload['official_likelihood_executed']}`",
        f"Trial type: `{payload['trial_type']}`",
        "",
        "## Lambda Grid",
    ]
    for lam in payload["lambda_grid"]:
        row = payload["trial_rows"].get(str(lam), {})
        lines.append(f"- `{lam}`: total finite chi2 `{row.get('total_finite_chi2')}`, delta `{row.get('delta_chi2_total_available')}`")
    lines.extend(["", payload["next_required_action"], ""])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(run_official=True), indent=2))
