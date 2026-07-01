from __future__ import annotations

import csv
import json
import math
from pathlib import Path

import numpy as np


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_camb_gr_baseline_export.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_camb_gr_baseline_export.json")
SPECTRA_PATH = Path("outputs/reports/p0_eft_janus_z4_camb_gr_baseline_spectra.csv")
FIELDS = ["ell", "cl_tt", "cl_te", "cl_ee", "cl_pp"]
T_CMB_MUK = 2.7255e6


def _from_dell(ell: np.ndarray, dell: np.ndarray, channel: str) -> np.ndarray:
    denom = np.square(ell * (ell + 1.0)) if channel == "pp" else ell * (ell + 1.0)
    return np.where(denom > 0.0, dell * (2.0 * math.pi) / denom, 0.0)


def _ell_grid() -> list[int]:
    return sorted(set(list(range(2, 202, 10)) + list(range(202, 1202, 20)) + list(range(1202, 2509, 40)) + [2508]))


def camb_gr_rows(ells: list[int] | None = None) -> list[dict[str, float]]:
    try:
        import camb
    except Exception as exc:  # pragma: no cover
        raise RuntimeError(f"CAMB unavailable: {type(exc).__name__}: {exc}") from exc

    ell = np.array(ells or _ell_grid(), dtype=float)
    pars = camb.CAMBparams()
    pars.set_cosmology(H0=67.4, ombh2=0.02237, omch2=0.1200, tau=0.054, YHe=0.2454)
    pars.InitPower.set_params(As=2.1e-9, ns=0.965)
    pars.set_for_lmax(int(np.max(ell)) + 64, lens_potential_accuracy=1)
    results = camb.get_results(pars)
    powers = results.get_cmb_power_spectra(pars, CMB_unit="muK", raw_cl=False)
    total = powers["total"]
    camb_ell = np.arange(total.shape[0], dtype=float)
    lens = results.get_lens_potential_cls(lmax=int(np.max(ell)) + 64, raw_cl=False)
    lens_ell = np.arange(lens.shape[0], dtype=float)

    tt_dell = np.interp(ell, camb_ell, total[:, 0]) / (T_CMB_MUK * T_CMB_MUK)
    ee_dell = np.interp(ell, camb_ell, total[:, 1]) / (T_CMB_MUK * T_CMB_MUK)
    te_dell = np.interp(ell, camb_ell, total[:, 3]) / (T_CMB_MUK * T_CMB_MUK)
    pp_dell = np.interp(ell, lens_ell, lens[:, 0])
    return [
        {
            "ell": int(e),
            "cl_tt": float(tt),
            "cl_te": float(te),
            "cl_ee": float(ee),
            "cl_pp": float(pp),
        }
        for e, tt, te, ee, pp in zip(
            ell,
            _from_dell(ell, tt_dell, "tt"),
            _from_dell(ell, te_dell, "te"),
            _from_dell(ell, ee_dell, "ee"),
            _from_dell(ell, pp_dell, "pp"),
        )
    ]


def build_payload() -> dict:
    rows = camb_gr_rows()
    finite = all(math.isfinite(float(row[field])) for row in rows for field in FIELDS)
    increasing = all(rows[idx]["ell"] < rows[idx + 1]["ell"] for idx in range(len(rows) - 1))
    positive_auto = all(row["cl_tt"] >= 0.0 and row["cl_ee"] >= 0.0 and row["cl_pp"] >= 0.0 for row in rows)
    SPECTRA_PATH.parent.mkdir(parents=True, exist_ok=True)
    with SPECTRA_PATH.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=FIELDS)
        writer.writeheader()
        writer.writerows(rows)
    return {
        "status": "janus-z4-camb-gr-baseline-export",
        "backend": "CAMB",
        "z4_sector_enabled": False,
        "negative_sector_enabled": False,
        "torsion_enabled": False,
        "spectra_path": str(SPECTRA_PATH),
        "row_count": len(rows),
        "ell_min": rows[0]["ell"],
        "ell_max": rows[-1]["ell"],
        "native_schema_fields": FIELDS,
        "finite_tt_te_ee_pp_produced": finite,
        "ell_grid_strictly_increasing": increasing,
        "positive_auto_spectra": positive_auto,
        "gr_baseline_export_ready": finite and increasing and positive_auto,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2, sort_keys=True), encoding="utf-8")
    lines = [
        "# Janus Z4 CAMB GR Baseline Export",
        "",
        f"Backend: `{payload['backend']}`",
        f"Spectra path: `{payload['spectra_path']}`",
        f"Rows: `{payload['row_count']}`",
        f"Ready: `{payload['gr_baseline_export_ready']}`",
        "",
        "This is the strict GR/Z4-off reference exported in the native spectra schema.",
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
