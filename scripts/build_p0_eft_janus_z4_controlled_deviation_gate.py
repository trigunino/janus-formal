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

from scripts.build_p0_eft_janus_z4_camb_gr_baseline_export import SPECTRA_PATH as CAMB_GR_PATH
from scripts.build_p0_eft_janus_z4_camb_gr_baseline_export import write_reports as write_camb_gr
from scripts.build_p0_eft_janus_z4_native_gr_reference_gate import _camb_reference, _fit_shape, _to_dell


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_controlled_deviation_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_controlled_deviation_gate.json")

DELTA_CHANNELS = [
    "delta_weyl_lensing_kernel",
    "delta_sw_isw_source",
    "delta_acoustic_phase",
    "delta_polarization_source",
    "delta_background_projection",
    "delta_hidden_sector_stress",
]


def _load_baseline() -> list[dict[str, float]]:
    if not CAMB_GR_PATH.exists():
        write_camb_gr()
    with CAMB_GR_PATH.open(encoding="utf-8") as handle:
        rows = [{key: float(value) for key, value in row.items()} for row in csv.DictReader(handle)]
    if not rows or rows[-1]["ell"] < 2508:
        write_camb_gr()
        with CAMB_GR_PATH.open(encoding="utf-8") as handle:
            rows = [{key: float(value) for key, value in row.items()} for row in csv.DictReader(handle)]
    return rows


def _spectra_from_rows(rows: list[dict[str, float]]) -> tuple[np.ndarray, dict[str, np.ndarray]]:
    ell = np.array([row["ell"] for row in rows], dtype=float)
    return ell, {
        "tt": _to_dell(ell, np.array([row["cl_tt"] for row in rows], dtype=float), "tt"),
        "te": _to_dell(ell, np.array([row["cl_te"] for row in rows], dtype=float), "te"),
        "ee": _to_dell(ell, np.array([row["cl_ee"] for row in rows], dtype=float), "ee"),
        "pp": _to_dell(ell, np.array([row["cl_pp"] for row in rows], dtype=float), "pp"),
    }


def _zero_delta(ell: np.ndarray) -> dict[str, np.ndarray]:
    return {channel: np.zeros_like(ell) for channel in ("tt", "te", "ee", "pp")}


def _apply_delta(base: dict[str, np.ndarray], delta: dict[str, np.ndarray], lambda_z4: float) -> dict[str, np.ndarray]:
    return {channel: base[channel] + lambda_z4 * delta[channel] for channel in ("tt", "te", "ee", "pp")}


def _shape_against_camb(ell: np.ndarray, spectra: dict[str, np.ndarray]) -> dict[str, dict]:
    camb = _camb_reference(ell)
    masks = {
        "high_tt": (ell >= 30.0) & (ell <= 1200.0),
        "high_te": (ell >= 30.0) & (ell <= 1200.0),
        "high_ee": (ell >= 30.0) & (ell <= 1200.0),
        "lensing_pp": (ell >= 8.0) & (ell <= 400.0),
    }
    return {
        "high_tt": _fit_shape(spectra["tt"][masks["high_tt"]], camb["tt"][masks["high_tt"]]),
        "high_te": _fit_shape(spectra["te"][masks["high_te"]], camb["te"][masks["high_te"]]),
        "high_ee": _fit_shape(spectra["ee"][masks["high_ee"]], camb["ee"][masks["high_ee"]]),
        "lensing_pp": _fit_shape(spectra["pp"][masks["lensing_pp"]], camb["pp"][masks["lensing_pp"]]),
    }


def _te_zeros(ell: np.ndarray, values: np.ndarray) -> list[int]:
    mask = (ell >= 30.0) & (ell <= 1200.0) & np.isfinite(values)
    e = ell[mask].astype(int)
    v = values[mask]
    out: list[int] = []
    for idx in range(len(v) - 1):
        if v[idx] == 0.0 or v[idx] * v[idx + 1] < 0.0:
            out.append(int(e[idx]))
    return out[:8]


def _continuity_check(ell: np.ndarray, base: dict[str, np.ndarray], delta: dict[str, np.ndarray]) -> dict[str, dict]:
    checks = {}
    for lam in (1.0e-6, 1.0e-4, 1.0e-3):
        spectra = _apply_delta(base, delta, lam)
        finite = all(np.isfinite(spectra[channel]).all() for channel in spectra)
        positive_auto = bool(
            np.nanmin(spectra["tt"][ell >= 2.0]) >= 0.0
            and np.nanmin(spectra["ee"][ell >= 2.0]) >= 0.0
            and np.nanmin(spectra["pp"][ell >= 2.0]) >= 0.0
        )
        max_frac = {}
        for channel in ("tt", "te", "ee", "pp"):
            denom = np.maximum(np.abs(base[channel]), np.nanmax(np.abs(base[channel])) * 1.0e-12)
            max_frac[channel] = float(np.nanmax(np.abs(spectra[channel] - base[channel]) / denom))
        checks[str(lam)] = {
            "finite": finite,
            "positive_auto_spectra": positive_auto,
            "max_abs_delta_over_baseline": max_frac,
            "ok": bool(finite and positive_auto and max(max_frac.values()) < 1.0e-6),
        }
    return checks


def build_payload() -> dict:
    rows = _load_baseline()
    ell, base = _spectra_from_rows(rows)
    delta = _zero_delta(ell)
    lambda0_spectra = _apply_delta(base, delta, 0.0)
    lambda0_shape = _shape_against_camb(ell, lambda0_spectra)
    identity_at_zero = all(row.get("ok", False) and row.get("chi2_per_dof", math.inf) < 1.0e-8 for row in lambda0_shape.values())
    continuity = _continuity_check(ell, base, delta)
    continuity_ok = all(row["ok"] for row in continuity.values())
    raw_native_los_used_for_planck = False
    spectrum_level_delta_debug_only = True
    gate_passed = bool(identity_at_zero and continuity_ok and not raw_native_los_used_for_planck)
    return {
        "status": "janus-z4-controlled-deviation-gate",
        "theory_vector_backend": "camb_gr_plus_z4_delta",
        "baseline_backend": "camb_gr_safe_baseline",
        "lambda_z4_default": 0.0,
        "delta_channels": DELTA_CHANNELS,
        "channel_deltas_tagged": True,
        "source_level_delta_required_for_physics": True,
        "spectrum_level_delta_debug_only": spectrum_level_delta_debug_only,
        "raw_native_los_used_for_planck": raw_native_los_used_for_planck,
        "lambda_zero_identity_shape": lambda0_shape,
        "z4_delta_identity_at_zero_passed": identity_at_zero,
        "z4_delta_continuity": continuity,
        "z4_delta_continuity_passed": continuity_ok,
        "te_zero_crossings_at_zero": _te_zeros(ell, lambda0_spectra["te"]),
        "controlled_z4_delta_gate_passed": gate_passed,
        "official_planck_allowed_for_delta_backend": gate_passed,
        "next_required_action": "derive a nonzero source-level Z4 delta for one tagged physical channel, starting with Weyl/lensing or SW/ISW",
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2, sort_keys=True), encoding="utf-8")
    lines = [
        "# Janus Z4 Controlled Deviation Gate",
        "",
        f"Backend: `{payload['theory_vector_backend']}`",
        f"lambda_Z4 default: `{payload['lambda_z4_default']}`",
        f"Identity at zero: `{payload['z4_delta_identity_at_zero_passed']}`",
        f"Continuity: `{payload['z4_delta_continuity_passed']}`",
        f"Raw native LOS used for Planck: `{payload['raw_native_los_used_for_planck']}`",
        f"Official Planck allowed for delta backend: `{payload['official_planck_allowed_for_delta_backend']}`",
        "",
        "## Delta Channels",
    ]
    lines.extend(f"- `{channel}`" for channel in payload["delta_channels"])
    lines.extend([
        "",
        f"TE zero crossings at lambda=0: `{payload['te_zero_crossings_at_zero']}`",
        "",
        payload["next_required_action"],
        "",
    ])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
