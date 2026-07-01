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

from scripts.build_p0_eft_janus_z4_native_cmb_transfer_solver import SPECTRA_PATH, write_reports as write_native


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_native_gr_reference_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_native_gr_reference_gate.json")


def _load_native_rows() -> list[dict[str, float]]:
    if not SPECTRA_PATH.exists():
        write_native()
    with SPECTRA_PATH.open(encoding="utf-8") as handle:
        rows = [{key: float(value) for key, value in row.items()} for row in csv.DictReader(handle)]
    if rows and rows[-1]["ell"] < 2508:
        write_native()
        with SPECTRA_PATH.open(encoding="utf-8") as handle:
            rows = [{key: float(value) for key, value in row.items()} for row in csv.DictReader(handle)]
    return rows


def _camb_reference(ell: np.ndarray) -> dict[str, np.ndarray]:
    try:
        import camb
    except Exception as exc:  # pragma: no cover - environment diagnostic
        raise RuntimeError(f"CAMB unavailable: {type(exc).__name__}: {exc}") from exc

    pars = camb.CAMBparams()
    pars.set_cosmology(H0=67.4, ombh2=0.02237, omch2=0.1200, tau=0.054, YHe=0.2454)
    pars.InitPower.set_params(As=2.1e-9, ns=0.965)
    pars.set_for_lmax(int(max(ell)) + 64, lens_potential_accuracy=1)
    results = camb.get_results(pars)
    powers = results.get_cmb_power_spectra(pars, CMB_unit="muK", raw_cl=False)
    total = powers["total"]
    camb_ell = np.arange(total.shape[0], dtype=float)
    lens = results.get_lens_potential_cls(lmax=int(max(ell)) + 64, raw_cl=False)
    lens_ell = np.arange(lens.shape[0], dtype=float)

    return {
        "tt": np.interp(ell, camb_ell, total[:, 0]),
        "ee": np.interp(ell, camb_ell, total[:, 1]),
        "te": np.interp(ell, camb_ell, total[:, 3]),
        "pp": np.interp(ell, lens_ell, lens[:, 0]),
    }


def _to_dell(ell: np.ndarray, cl: np.ndarray, channel: str) -> np.ndarray:
    if channel == "pp":
        return np.square(ell * (ell + 1.0)) * cl / (2.0 * math.pi)
    return ell * (ell + 1.0) * cl / (2.0 * math.pi)


def _fit_shape(native: np.ndarray, reference: np.ndarray) -> dict:
    mask = np.isfinite(native) & np.isfinite(reference) & (np.abs(reference) > 0.0)
    n = int(np.sum(mask))
    if n < 8:
        return {"points": n, "ok": False, "reason": "not enough finite points"}
    x = native[mask]
    y = reference[mask]
    amp = float(np.dot(x, y) / max(np.dot(x, x), 1.0e-300))
    residual = amp * x - y
    sigma = np.maximum(np.abs(y) * 0.05, np.nanmax(np.abs(y)) * 1.0e-4)
    chi2 = float(np.sum(np.square(residual / sigma)))
    return {
        "points": n,
        "best_shape_amplitude": amp,
        "chi2_shape": chi2,
        "chi2_per_dof": chi2 / max(n - 1, 1),
        "max_abs_fractional_residual": float(np.nanmax(np.abs(residual) / np.maximum(np.abs(y), 1.0e-300))),
        "ok": bool(chi2 / max(n - 1, 1) < 5.0),
    }


def _peak_shift(ell: np.ndarray, native: np.ndarray, reference: np.ndarray) -> dict:
    mask = (ell >= 30.0) & (ell <= 450.0)
    native_peak = int(ell[mask][np.argmax(native[mask])])
    reference_peak = int(ell[mask][np.argmax(reference[mask])])
    return {
        "native_peak_ell": native_peak,
        "reference_peak_ell": reference_peak,
        "ell_shift": native_peak - reference_peak,
        "ok": abs(native_peak - reference_peak) <= 10,
    }


def build_payload() -> dict:
    rows = _load_native_rows()
    ell = np.array([row["ell"] for row in rows], dtype=float)
    camb = _camb_reference(ell)
    native = {
        "tt": _to_dell(ell, np.array([row["cl_tt"] for row in rows], dtype=float), "tt"),
        "te": _to_dell(ell, np.array([row["cl_te"] for row in rows], dtype=float), "te"),
        "ee": _to_dell(ell, np.array([row["cl_ee"] for row in rows], dtype=float), "ee"),
        "pp": _to_dell(ell, np.array([row["cl_pp"] for row in rows], dtype=float), "pp"),
    }
    band_masks = {
        "low_tt": (ell >= 2.0) & (ell <= 29.0),
        "high_tt": (ell >= 30.0) & (ell <= 1200.0),
        "high_te": (ell >= 30.0) & (ell <= 1200.0),
        "high_ee": (ell >= 30.0) & (ell <= 1200.0),
        "lensing_pp": (ell >= 8.0) & (ell <= 400.0),
    }
    shape = {
        "low_tt": _fit_shape(native["tt"][band_masks["low_tt"]], camb["tt"][band_masks["low_tt"]]),
        "high_tt": _fit_shape(native["tt"][band_masks["high_tt"]], camb["tt"][band_masks["high_tt"]]),
        "high_te": _fit_shape(native["te"][band_masks["high_te"]], camb["te"][band_masks["high_te"]]),
        "high_ee": _fit_shape(native["ee"][band_masks["high_ee"]], camb["ee"][band_masks["high_ee"]]),
        "lensing_pp": _fit_shape(native["pp"][band_masks["lensing_pp"]], camb["pp"][band_masks["lensing_pp"]]),
    }
    peak = _peak_shift(ell, native["tt"], camb["tt"])
    gate_passed = bool(all(row.get("ok", False) for row in shape.values()) and peak["ok"])
    return {
        "status": "janus-z4-native-gr-reference-gate",
        "reference_solver": "CAMB",
        "reference_model": "vanilla GR baseline with fixed Planck-like background parameters",
        "z4_sector_enabled": False,
        "negative_sector_enabled": False,
        "torsion_enabled": False,
        "compressed_lcdm_parameters_used_for_validation": False,
        "native_spectra_path": str(SPECTRA_PATH),
        "ell_min": int(ell[0]),
        "ell_max": int(ell[-1]),
        "shape_only_amplitude_fit": True,
        "shape": shape,
        "tt_first_peak": peak,
        "native_gr_matches_standard_gr": gate_passed,
        "z4_corrections_allowed": gate_passed,
        "verdict": (
            "Native GR baseline matches CAMB sufficiently for Z4 corrections."
            if gate_passed
            else "Native GR baseline does not match CAMB; Z4 corrections are premature."
        ),
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2, sort_keys=True), encoding="utf-8")
    lines = [
        "# Janus Z4 Native GR Reference Gate",
        "",
        f"Status: `{payload['status']}`",
        f"Reference solver: `{payload['reference_solver']}`",
        f"Native GR matches standard GR: `{payload['native_gr_matches_standard_gr']}`",
        f"Z4 corrections allowed: `{payload['z4_corrections_allowed']}`",
        "",
        "## Shape Gates",
    ]
    for name, row in payload["shape"].items():
        lines.append(f"- `{name}`: ok `{row.get('ok')}`, chi2/dof `{row.get('chi2_per_dof')}`")
    lines.extend([
        "",
        "## TT First Peak",
        f"- native ell: `{payload['tt_first_peak']['native_peak_ell']}`",
        f"- CAMB ell: `{payload['tt_first_peak']['reference_peak_ell']}`",
        f"- shift: `{payload['tt_first_peak']['ell_shift']}`",
        "",
        payload["verdict"],
        "",
    ])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
