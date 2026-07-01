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
from scripts.build_p0_eft_janus_z4_lensing_shape_delta_gate import _shape_kernel_response
from scripts.run_p0_eft_janus_z4_official_planck_lensing_shape_delta_trial import (
    LAMBDAS,
    LIKELIHOODS,
    _run_likelihood,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_lensing_component_projection_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_lensing_component_projection_gate.json")
SPECTRA_DIR = Path("outputs/reports/z4_lensing_component_projection_spectra")
COMPONENTS = ("amplitude_only", "shape_only", "full")


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


def _component_response(ell: np.ndarray, component: str) -> np.ndarray:
    q_full = _shape_kernel_response(ell)
    mask = (ell >= 8.0) & (ell <= 1000.0)
    mean = float(np.mean(q_full[mask]))
    if component == "amplitude_only":
        return np.full_like(ell, mean)
    if component == "shape_only":
        return q_full - mean
    if component == "full":
        return q_full
    raise ValueError(component)


def _write_component_spectra(rows: list[dict[str, float]], component: str, lam: float) -> Path:
    SPECTRA_DIR.mkdir(parents=True, exist_ok=True)
    ell = np.array([row["ell"] for row in rows], dtype=float)
    response = _component_response(ell, component)
    path = SPECTRA_DIR / f"{component}_lambda_{_tag(lam)}.csv"
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=["ell", "cl_tt", "cl_te", "cl_ee", "cl_pp"])
        writer.writeheader()
        for row, q in zip(rows, response):
            writer.writerow({
                "ell": int(row["ell"]),
                "cl_tt": row["cl_tt"],
                "cl_te": row["cl_te"],
                "cl_ee": row["cl_ee"],
                "cl_pp": row["cl_pp"] * (1.0 + lam * float(q)),
            })
    return path


def _response_stats(rows: list[dict[str, float]]) -> dict:
    ell = np.array([row["ell"] for row in rows], dtype=float)
    stats = {}
    for component in COMPONENTS:
        q = _component_response(ell, component)
        mask = (ell >= 8.0) & (ell <= 1000.0)
        stats[component] = {
            "mean": float(np.mean(q[mask])),
            "rms": float(np.sqrt(np.mean(np.square(q[mask])))),
            "max_abs": float(np.max(np.abs(q[mask]))),
            "sign_changes": int(np.sum(np.signbit(q[mask][:-1]) != np.signbit(q[mask][1:]))),
        }
    return stats


def _trial(run_official: bool) -> dict:
    rows = _load_rows()
    out = {}
    for component in COMPONENTS:
        out[component] = {}
        for lam in LAMBDAS:
            path = _write_component_spectra(rows, component, lam)
            channels = {}
            if run_official:
                channels = {name: _run_likelihood(like, path) for name, like in LIKELIHOODS.items()}
            finite = {name: row["chi2"] for name, row in channels.items() if row.get("finite")}
            out[component][str(lam)] = {
                "spectra_path": str(path),
                "channels": channels,
                "finite_channel_chi2": finite,
                "total_finite_chi2": float(sum(finite.values())) if finite else None,
            }
    for component, rows_by_lambda in out.items():
        baseline = rows_by_lambda.get("0.0", {}).get("total_finite_chi2")
        for row in rows_by_lambda.values():
            total = row.get("total_finite_chi2")
            row["delta_chi2_total_available"] = (
                float(total - baseline)
                if total is not None and baseline is not None
                else None
            )
    return out


def _best(rows_by_lambda: dict) -> dict:
    candidates = [
        {"lambda": lam, "delta_chi2": row.get("delta_chi2_total_available")}
        for lam, row in rows_by_lambda.items()
        if row.get("delta_chi2_total_available") is not None
    ]
    return min(candidates, key=lambda row: row["delta_chi2"], default={"lambda": None, "delta_chi2": None})


def build_payload(run_official: bool = False) -> dict:
    rows = _load_rows()
    trial = _trial(run_official)
    best = {component: _best(trial[component]) for component in COMPONENTS}
    strongest = min(
        [row for row in best.values() if row["delta_chi2"] is not None],
        key=lambda row: row["delta_chi2"],
        default={"lambda": None, "delta_chi2": None},
    )
    negligible = bool(strongest["delta_chi2"] is None or abs(strongest["delta_chi2"]) < 1.0)
    return {
        "status": "janus-z4-lensing-component-projection-gate",
        "backend": "camb_gr_plus_z4_delta",
        "direct_Cl_patch": False,
        "native_toy_los_used": False,
        "components": list(COMPONENTS),
        "lambda_grid": list(LAMBDAS),
        "official_likelihood_requested": run_official,
        "official_likelihood_executed": any(
            bool(row["channels"])
            for component in trial.values()
            for row in component.values()
        ),
        "response_stats": _response_stats(rows),
        "trial": trial,
        "best_by_component": best,
        "strongest_available_response": strongest,
        "lensing_component_response_negligible": negligible,
        "lensing_shape_delta_observationally_useful": False if negligible else None,
        "lensing_shape_delta_rescues_planck": False,
        "recommended_status": "demote_lensing_only_to_diagnostic" if negligible else "inspect_lensing_projection_further",
        "next_required_action": "open late-ISW source-level delta gate; do not treat lensing-only as Planck rescue",
    }


def write_reports(run_official: bool = True) -> dict:
    payload = build_payload(run_official=run_official)
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2, sort_keys=True), encoding="utf-8")
    lines = [
        "# Janus Z4 Lensing Component Projection Gate",
        "",
        f"Official likelihood requested: `{payload['official_likelihood_requested']}`",
        f"Official likelihood executed: `{payload['official_likelihood_executed']}`",
        f"Negligible response: `{payload['lensing_component_response_negligible']}`",
        f"Recommended status: `{payload['recommended_status']}`",
        "",
        "## Best by Component",
    ]
    for component, row in payload["best_by_component"].items():
        lines.append(f"- `{component}`: lambda `{row['lambda']}`, delta chi2 `{row['delta_chi2']}`")
    lines.extend(["", payload["next_required_action"], ""])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(run_official=True), indent=2))
