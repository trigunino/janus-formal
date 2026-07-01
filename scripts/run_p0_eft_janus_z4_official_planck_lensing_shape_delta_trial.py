from __future__ import annotations

import csv
import json
import math
import sys
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))
SRC = ROOT / "src"
if str(SRC) not in sys.path:
    sys.path.insert(0, str(SRC))

from scripts.build_p0_eft_janus_z4_camb_gr_baseline_export import SPECTRA_PATH as CAMB_GR_PATH
from scripts.build_p0_eft_janus_z4_camb_gr_baseline_export import write_reports as write_camb_gr
from scripts.build_p0_eft_janus_z4_lensing_shape_delta_gate import _shape_kernel_response
from scripts.build_p0_eft_janus_z4_nonzero_planck_eligibility_gate import build_payload as eligibility_payload


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_official_planck_lensing_shape_delta_trial.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_official_planck_lensing_shape_delta_trial.json")
SPECTRA_DIR = Path("outputs/reports/z4_lensing_shape_delta_trial_spectra")
LAMBDAS = (-1.0e-2, -1.0e-3, 0.0, 1.0e-3, 1.0e-2)
LIKELIHOODS = {
    "lowl_TT": "planck_2018_lowl.TT",
    "lowl_EE": "planck_2018_lowl.EE",
    "lensing": "planck_2018_lensing.clik",
    "highl_TT": "planck_2018_highl_plik.TT",
    "highl_TE": "planck_2018_highl_plik.TE",
    "highl_EE": "planck_2018_highl_plik.EE",
    "highl_TTTEEE": "planck_2018_highl_plik.TTTEEE",
}


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


def _tag(lam: float) -> str:
    if lam == 0.0:
        return "p0"
    sign = "m" if lam < 0 else "p"
    return f"{sign}{abs(lam):.0e}".replace("+", "").replace("-", "").replace(".", "p")


def _write_delta_spectra(rows: list[dict[str, float]], lam: float) -> Path:
    SPECTRA_DIR.mkdir(parents=True, exist_ok=True)
    ell = np.array([row["ell"] for row in rows], dtype=float)
    q_l = _shape_kernel_response(ell)
    path = SPECTRA_DIR / f"lambda_{_tag(lam)}.csv"
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=["ell", "cl_tt", "cl_te", "cl_ee", "cl_pp"])
        writer.writeheader()
        for row, q in zip(rows, q_l):
            writer.writerow({
                "ell": int(row["ell"]),
                "cl_tt": row["cl_tt"],
                "cl_te": row["cl_te"],
                "cl_ee": row["cl_ee"],
                "cl_pp": row["cl_pp"] * (1.0 + lam * float(q)),
            })
    return path


def _band_response(rows: list[dict[str, float]], lam: float) -> dict[str, float]:
    ell = np.array([row["ell"] for row in rows], dtype=float)
    q_l = _shape_kernel_response(ell)
    out = {}
    for low, high in ((8, 40), (40, 100), (100, 400), (400, 1000)):
        mask = (ell >= low) & (ell < high)
        out[f"delta_Cphiphi_band_{low}_{high}"] = float(lam * np.mean(q_l[mask]))
    return out


def _reference_point(info: dict) -> dict[str, float]:
    from cobaya.input import update_info

    updated = update_info(info)
    point = {}
    for name, spec in updated["params"].items():
        if not isinstance(spec, dict) or "prior" not in spec or "value" in spec:
            continue
        ref = spec.get("ref") or {}
        if "loc" in ref:
            point[name] = float(ref["loc"])
        elif "min" in spec["prior"] and "max" in spec["prior"]:
            point[name] = 0.5 * (float(spec["prior"]["min"]) + float(spec["prior"]["max"]))
        else:
            point[name] = 0.0
    return point


def _run_likelihood(component: str, spectra_path: Path) -> dict:
    from cobaya.model import get_model

    info = {
        "theory": {"janus_lab.z4_cmb_cobaya.JanusZ4NativeBoltzmann": {"spectra_path": str(spectra_path)}},
        "likelihood": {component: None},
        "params": {
            "janus_dummy": {"value": 0.0},
            "A_planck": {"value": 1.0},
        },
        "packages_path": "external/cobaya_packages",
        "stop_at_error": False,
    }
    try:
        point = _reference_point(info)
        model = get_model(info)
        loglikes, derived = model.loglikes(point, return_derived=True)
        loglike = float(loglikes[0])
        chi2 = -2.0 * loglike if math.isfinite(loglike) else math.inf
        return {
            "executed": True,
            "finite": math.isfinite(chi2),
            "chi2": chi2,
            "loglike": loglike,
            "sampled_nuisance_count": len(point),
            "derived": [float(value) for value in derived],
            "error": None,
        }
    except Exception as exc:  # pragma: no cover - environment-dependent audit data
        return {
            "executed": False,
            "finite": False,
            "chi2": None,
            "loglike": None,
            "sampled_nuisance_count": 0,
            "derived": [],
            "error": f"{type(exc).__name__}: {exc}",
        }


def build_payload(run_official: bool = False) -> dict:
    eligibility = eligibility_payload()
    rows = _load_rows()
    spectra_paths = {str(lam): str(_write_delta_spectra(rows, lam)) for lam in LAMBDAS}
    band_response = {str(lam): _band_response(rows, lam) for lam in LAMBDAS}
    trial_rows = {}
    if run_official and eligibility["nonzero_z4_official_likelihood_allowed"]:
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
    for lam, row in trial_rows.items():
        total = row.get("total_finite_chi2")
        row["delta_chi2_total_available"] = (
            float(total - baseline_total)
            if total is not None and baseline_total is not None
            else None
        )
    return {
        "status": "official-planck-lensing-shape-delta-trial",
        "is_planck_success_verdict": False,
        "eligibility_gate_passed": bool(eligibility["nonzero_z4_official_likelihood_allowed"]),
        "backend": "camb_gr_plus_z4_delta",
        "delta_channels_enabled": ["weyl_lensing_shape"],
        "native_toy_los_used": False,
        "full_native_z4_solver_used": False,
        "lambda_grid": list(LAMBDAS),
        "spectra_paths": spectra_paths,
        "band_response": band_response,
        "official_likelihood_requested": run_official,
        "official_likelihood_executed": bool(trial_rows),
        "trial_rows": trial_rows,
        "next_required_action": "inspect signed delta_chi2; separate amplitude-only and shape-only projections if any channel improves",
    }


def write_reports(run_official: bool = True) -> dict:
    payload = build_payload(run_official=run_official)
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2, sort_keys=True), encoding="utf-8")
    lines = [
        "# Official Planck Lensing Shape Delta Trial",
        "",
        f"Eligibility passed: `{payload['eligibility_gate_passed']}`",
        f"Planck success verdict: `{payload['is_planck_success_verdict']}`",
        f"Official likelihood requested: `{payload['official_likelihood_requested']}`",
        f"Official likelihood executed: `{payload['official_likelihood_executed']}`",
        f"Backend: `{payload['backend']}`",
        f"Delta channels: `{payload['delta_channels_enabled']}`",
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
