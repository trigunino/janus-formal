from __future__ import annotations

import csv
import json
from pathlib import Path

import numpy as np


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_highl_residual_diagnostic_report.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_highl_residual_diagnostic_report.json")
TRIAL_JSON = Path("outputs/reports/p0_eft_janus_z4_closed_boltzmann_candidate_highl_decomposition_trial.json")
ACCOUNTING_JSON = Path("outputs/reports/p0_eft_janus_z4_nonoverlapping_likelihood_accounting_gate.json")

BANDS = ((30, 200), (200, 600), (600, 1000), (1000, 1600), (1600, 2400))


def _load(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8")) if path.exists() else {}


def _read_spectra(path: Path) -> dict[str, np.ndarray]:
    with path.open(encoding="utf-8") as handle:
        rows = [{key: float(value) for key, value in row.items()} for row in csv.DictReader(handle)]
    return {key: np.array([row[key] for row in rows], dtype=float) for key in rows[0]}


def _relative(candidate: np.ndarray, baseline: np.ndarray) -> np.ndarray:
    denom = np.where(np.abs(baseline) > 1.0e-30, np.abs(baseline), 1.0)
    return (candidate - baseline) / denom


def _band_stats(ell: np.ndarray, residual: np.ndarray) -> dict:
    out = {}
    for lo, hi in BANDS:
        mask = (ell >= lo) & (ell < hi)
        y = residual[mask]
        out[f"{lo}_{hi}"] = {
            "mean": float(np.mean(y)),
            "max_abs": float(np.max(np.abs(y))),
            "rms": float(np.sqrt(np.mean(np.square(y)))),
        }
    return out


def _peak_shift(ell: np.ndarray, baseline: np.ndarray, candidate: np.ndarray, lo: int, hi: int) -> int:
    mask = (ell >= lo) & (ell < hi)
    base_ell = ell[mask][int(np.argmax(baseline[mask]))]
    cand_ell = ell[mask][int(np.argmax(candidate[mask]))]
    return int(cand_ell - base_ell)


def _zero_shift(ell: np.ndarray, baseline: np.ndarray, candidate: np.ndarray, lo: int, hi: int) -> int | None:
    mask = (ell >= lo) & (ell < hi)
    e = ell[mask]
    base = baseline[mask]
    cand = candidate[mask]
    base_cross = np.where(np.signbit(base[:-1]) != np.signbit(base[1:]))[0]
    cand_cross = np.where(np.signbit(cand[:-1]) != np.signbit(cand[1:]))[0]
    if len(base_cross) == 0 or len(cand_cross) == 0:
        return None
    return int(e[cand_cross[0]] - e[base_cross[0]])


def build_payload() -> dict:
    trial = _load(TRIAL_JSON)
    accounting = _load(ACCOUNTING_JSON)
    baseline = _read_spectra(Path(trial["baseline_spectra_path"]))
    candidate = _read_spectra(Path(trial["candidate_spectra_path"]))
    ell = baseline["ell"]
    residuals = {
        "TT": _relative(candidate["cl_tt"], baseline["cl_tt"]),
        "TE": _relative(candidate["cl_te"], baseline["cl_te"]),
        "EE": _relative(candidate["cl_ee"], baseline["cl_ee"]),
    }
    return {
        "status": "janus-z4-highl-residual-diagnostic-report",
        "source_trial": str(TRIAL_JSON),
        "source_accounting": str(ACCOUNTING_JSON),
        "band_residuals": {name: _band_stats(ell, residual) for name, residual in residuals.items()},
        "TT_peak_shifts": {
            "200_400": _peak_shift(ell, baseline["cl_tt"], candidate["cl_tt"], 200, 400),
            "400_700": _peak_shift(ell, baseline["cl_tt"], candidate["cl_tt"], 400, 700),
            "700_1100": _peak_shift(ell, baseline["cl_tt"], candidate["cl_tt"], 700, 1100),
        },
        "TE_zero_shifts": {
            "50_400": _zero_shift(ell, baseline["cl_te"], candidate["cl_te"], 50, 400),
            "400_900": _zero_shift(ell, baseline["cl_te"], candidate["cl_te"], 400, 900),
        },
        "EE_peak_shifts": {
            "200_500": _peak_shift(ell, baseline["cl_ee"], candidate["cl_ee"], 200, 500),
            "500_900": _peak_shift(ell, baseline["cl_ee"], candidate["cl_ee"], 500, 900),
            "900_1400": _peak_shift(ell, baseline["cl_ee"], candidate["cl_ee"], 900, 1400),
        },
        "smoothness_scores": {
            name: {
                "max_gradient": float(np.max(np.abs(np.gradient(residual)))),
                "second_difference_rms": float(np.sqrt(np.mean(np.square(np.diff(residual, n=2))))),
            }
            for name, residual in residuals.items()
        },
        "nonoverlap_accounting": {
            "combined_highl": accounting.get("nonoverlapping_total_combined_highl"),
            "decomposed_highl": accounting.get("nonoverlapping_total_decomposed_highl"),
            "legacy_overlapping_total_diagnostic_only": accounting.get("legacy_overlapping_total"),
        },
        "residual_report_complete": True,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2, sort_keys=True), encoding="utf-8")
    lines = [
        "# Janus Z4 High-L Residual Diagnostic Report",
        "",
        f"Complete: `{payload['residual_report_complete']}`",
        "",
        "## Non-overlap accounting",
        "",
    ]
    for key, value in payload["nonoverlap_accounting"].items():
        lines.append(f"- `{key}`: `{value}`")
    lines.extend(["", "## Peak and zero shifts", ""])
    lines.append(f"- TT peak shifts: `{payload['TT_peak_shifts']}`")
    lines.append(f"- TE zero shifts: `{payload['TE_zero_shifts']}`")
    lines.append(f"- EE peak shifts: `{payload['EE_peak_shifts']}`")
    REPORT_PATH.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
