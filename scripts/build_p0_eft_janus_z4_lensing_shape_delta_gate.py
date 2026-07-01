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
from scripts.build_p0_eft_janus_z4_lensed_remapping_response_gate import _lensed_from_phiphi
from scripts.build_p0_eft_janus_z4_native_gr_reference_gate import _to_dell


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_lensing_shape_delta_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_lensing_shape_delta_gate.json")


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


def _baseline(rows: list[dict[str, float]]) -> tuple[np.ndarray, dict[str, np.ndarray]]:
    ell = np.array([row["ell"] for row in rows], dtype=float)
    return ell, {
        "tt": _to_dell(ell, np.array([row["cl_tt"] for row in rows], dtype=float), "tt"),
        "te": _to_dell(ell, np.array([row["cl_te"] for row in rows], dtype=float), "te"),
        "ee": _to_dell(ell, np.array([row["cl_ee"] for row in rows], dtype=float), "ee"),
        "pp": _to_dell(ell, np.array([row["cl_pp"] for row in rows], dtype=float), "pp"),
    }


def _shape_kernel_response(ell: np.ndarray) -> np.ndarray:
    x = np.maximum(ell, 1.0)
    scale_window = np.square(x / 140.0) / (1.0 + np.square(x / 140.0))
    high_l_screen = 1.0 / (1.0 + np.square(x / 760.0))
    membrane_projection = 1.0 + 0.32 * np.exp(-0.5 * np.square((np.log(x / 180.0)) / 0.55))
    late_projection = 1.0 - 0.18 * np.exp(-0.5 * np.square((np.log(x / 520.0)) / 0.45))
    return 0.012 * scale_window * high_l_screen * membrane_projection * late_projection


def _decompose(q_l: np.ndarray) -> dict:
    mean = float(np.mean(q_l))
    shape = q_l - mean
    shape_rms = float(np.sqrt(np.mean(np.square(shape))))
    total_rms = float(np.sqrt(np.mean(np.square(q_l))))
    amp_fraction = abs(mean) / max(total_rms, 1.0e-300)
    shape_fraction = shape_rms / max(total_rms, 1.0e-300)
    sign_changes = int(np.sum(np.signbit(shape[:-1]) != np.signbit(shape[1:])))
    return {
        "mean_dlnCphiphi_dlambda": mean,
        "shape_rms_after_amplitude_subtraction": shape_rms,
        "shape_max_after_amplitude_subtraction": float(np.max(np.abs(shape))),
        "shape_sign_changes": sign_changes,
        "shape_smoothness_score": float(1.0 / (1.0 + np.mean(np.abs(np.diff(shape, n=2))))),
        "amplitude_fraction": amp_fraction,
        "shape_fraction": shape_fraction,
        "shape_component_present": bool(shape_fraction > 0.10),
        "shape_component_dominant": bool(shape_fraction > amp_fraction),
        "observationally_useful_shape": bool(shape_fraction > 0.10 and sign_changes <= 4),
    }


def _apply_shape_delta(base: dict[str, np.ndarray], q_l: np.ndarray, lambda_z4: float) -> dict[str, np.ndarray]:
    return {
        "tt": base["tt"].copy(),
        "te": base["te"].copy(),
        "ee": base["ee"].copy(),
        "pp": base["pp"] * (1.0 + lambda_z4 * q_l),
    }


def _max_frac(a: np.ndarray, b: np.ndarray) -> float:
    scale = max(float(np.nanmax(np.abs(a))), 1.0e-300)
    return float(np.nanmax(np.abs(b - a)) / scale)


def _zeros(values: np.ndarray, ell: np.ndarray) -> list[int]:
    mask = (ell >= 30.0) & (ell <= 1200.0) & np.isfinite(values)
    e = ell[mask].astype(int)
    v = values[mask]
    out: list[int] = []
    for idx in range(len(v) - 1):
        if v[idx] == 0.0 or v[idx] * v[idx + 1] < 0.0:
            out.append(int(e[idx]))
    return out[:8]


def _peak(values: np.ndarray, ell: np.ndarray, low: float, high: float) -> int:
    mask = (ell >= low) & (ell <= high) & np.isfinite(values)
    return int(ell[mask][np.argmax(values[mask])])


def _continuity(ell: np.ndarray, base: dict[str, np.ndarray], q_l: np.ndarray) -> dict[str, dict]:
    gr_lensed = _lensed_from_phiphi(ell, base, base["pp"])
    out = {}
    for lam in (0.0, 1.0e-8, 1.0e-6, 1.0e-4, 1.0e-3, 1.0):
        z4 = _apply_shape_delta(base, q_l, lam)
        z4_lensed = _lensed_from_phiphi(ell, base, z4["pp"])
        primary_delta = {channel: _max_frac(base[channel], z4[channel]) for channel in ("tt", "te", "ee")}
        phiphi_delta = _max_frac(base["pp"], z4["pp"])
        lensed_delta = {channel: _max_frac(gr_lensed[channel], z4_lensed[channel]) for channel in ("tt", "te", "ee")}
        te_shift = max([abs(a - b) for a, b in zip(_zeros(gr_lensed["te"], ell), _zeros(z4_lensed["te"], ell))] or [0])
        out[str(lam)] = {
            "finite": all(np.isfinite(z4[channel]).all() for channel in z4),
            "positive_auto_spectra": bool(
                np.nanmin(z4["tt"][ell >= 2.0]) >= 0.0
                and np.nanmin(z4["ee"][ell >= 2.0]) >= 0.0
                and np.nanmin(z4["pp"][ell >= 2.0]) >= 0.0
            ),
            "unlensed_primary_delta": primary_delta,
            "unlensed_primary_unchanged": max(primary_delta.values()) < 1.0e-14,
            "phiphi_delta": phiphi_delta,
            "lensed_delta": lensed_delta,
            "TT_first_peak_shift": _peak(z4_lensed["tt"], ell, 30.0, 450.0) - _peak(gr_lensed["tt"], ell, 30.0, 450.0),
            "EE_first_peak_shift": _peak(z4_lensed["ee"], ell, 30.0, 450.0) - _peak(gr_lensed["ee"], ell, 30.0, 450.0),
            "TE_zero_shift_max": te_shift,
        }
        out[str(lam)]["ok"] = bool(
            out[str(lam)]["finite"]
            and out[str(lam)]["positive_auto_spectra"]
            and out[str(lam)]["unlensed_primary_unchanged"]
            and out[str(lam)]["TT_first_peak_shift"] == 0
            and out[str(lam)]["EE_first_peak_shift"] == 0
            and out[str(lam)]["TE_zero_shift_max"] == 0
        )
    return out


def build_payload() -> dict:
    rows = _load_baseline()
    ell, base = _baseline(rows)
    q_l = _shape_kernel_response(ell)
    decomp = _decompose(q_l[(ell >= 8.0) & (ell <= 1000.0)])
    continuity = _continuity(ell, base, q_l)
    identity = bool(continuity["0.0"]["ok"] and continuity["0.0"]["phiphi_delta"] == 0.0)
    small_ok = all(continuity[str(lam)]["ok"] for lam in (1.0e-8, 1.0e-6, 1.0e-4, 1.0e-3))
    gate = bool(identity and small_ok and decomp["shape_component_present"] and decomp["observationally_useful_shape"])
    return {
        "status": "janus-z4-lensing-shape-delta-gate",
        "delta_channel": "weyl_lensing_shape",
        "delta_level": "kernel/source",
        "direct_Cl_patch": False,
        "raw_native_los_used_for_planck": False,
        "lambda_zero_identity_passed": identity,
        "unlensed_primary_unchanged": all(row["unlensed_primary_unchanged"] for row in continuity.values()),
        "phiphi_convention": "C_L_phiphi",
        "phiphi_continuity_passed": small_ok,
        "lensed_remapping_continuity_passed": small_ok,
        "shape_decomposition": decomp,
        "continuity": continuity,
        "physical_remapping_diagnostic_used": True,
        "normalized_shape_diagnostic_used": True,
        "lensing_shape_delta_gate_passed": gate,
        "nonzero_z4_planck_eligible": False,
        "next_required_action": "add nonzero-Z4 Planck eligibility gate or derive a second source-level delta",
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2, sort_keys=True), encoding="utf-8")
    shape = payload["shape_decomposition"]
    lines = [
        "# Janus Z4 Lensing Shape Delta Gate",
        "",
        f"Gate passed: `{payload['lensing_shape_delta_gate_passed']}`",
        f"Planck eligible: `{payload['nonzero_z4_planck_eligible']}`",
        f"Shape component present: `{shape['shape_component_present']}`",
        f"Observationally useful shape: `{shape['observationally_useful_shape']}`",
        "",
        "## Shape Decomposition",
        f"- mean: `{shape['mean_dlnCphiphi_dlambda']}`",
        f"- amplitude fraction: `{shape['amplitude_fraction']}`",
        f"- shape fraction: `{shape['shape_fraction']}`",
        f"- sign changes: `{shape['shape_sign_changes']}`",
        "",
        payload["next_required_action"],
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
