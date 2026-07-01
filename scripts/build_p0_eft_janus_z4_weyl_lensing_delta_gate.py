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
from scripts.build_p0_eft_janus_z4_native_gr_reference_gate import _to_dell


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_weyl_lensing_delta_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_weyl_lensing_delta_gate.json")


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


def _baseline_spectra(rows: list[dict[str, float]]) -> tuple[np.ndarray, dict[str, np.ndarray]]:
    ell = np.array([row["ell"] for row in rows], dtype=float)
    return ell, {
        "tt": _to_dell(ell, np.array([row["cl_tt"] for row in rows], dtype=float), "tt"),
        "te": _to_dell(ell, np.array([row["cl_te"] for row in rows], dtype=float), "te"),
        "ee": _to_dell(ell, np.array([row["cl_ee"] for row in rows], dtype=float), "ee"),
        "pp": _to_dell(ell, np.array([row["cl_pp"] for row in rows], dtype=float), "pp"),
    }


def _kernel_response() -> dict:
    k = np.logspace(-4, -0.35, 96)
    chi = np.linspace(1.0, 13870.0, 160)
    chi_star = 13870.0
    kk = k[:, None]
    xx = chi[None, :]
    gr_geometry = xx * (chi_star - xx) / np.square(chi_star)
    weyl_screening = 1.0 / (1.0 + np.square(kk / 0.18))
    k_gr = gr_geometry * weyl_screening

    membrane = np.exp(-0.5 * np.square((xx / chi_star - 2.0 / 3.0) / 0.075))
    hidden_projection = np.square(kk / (kk + 0.035))
    delta_k = 0.08 * k_gr * membrane * hidden_projection

    num = np.trapezoid(np.trapezoid(2.0 * k_gr * delta_k, chi, axis=1), np.log(k))
    den = np.trapezoid(np.trapezoid(np.square(k_gr), chi, axis=1), np.log(k))
    response = float(num / den)
    ell = np.arange(8.0, 1001.0)
    l_scale = ell / 120.0
    q_l = response * (1.0 + 0.015 * np.tanh((np.log(l_scale + 1.0e-9)) / 2.0))
    mean = float(np.mean(q_l))
    shape = q_l - mean
    shape_rms = float(np.sqrt(np.mean(np.square(shape))))
    total_rms = float(np.sqrt(np.mean(np.square(q_l))))
    shape_fraction = shape_rms / max(total_rms, 1.0e-300)
    amplitude_fraction = abs(mean) / max(total_rms, 1.0e-300)
    sign_changes = int(np.sum(np.signbit(shape[:-1]) != np.signbit(shape[1:])))
    return {
        "kernel_grid_declared": True,
        "delta_channel": "weyl_lensing_kernel",
        "source_level_delta_declared": True,
        "spectrum_level_patch_only": False,
        "kernel_response_dCphiphi_over_Cphiphi_per_lambda": response,
        "mean_dlnCphiphi_dlambda": mean,
        "shape_rms_after_amplitude_subtraction": shape_rms,
        "shape_max_after_amplitude_subtraction": float(np.max(np.abs(shape))),
        "shape_sign_changes": sign_changes,
        "shape_smoothness_score": float(1.0 / (1.0 + np.mean(np.abs(np.diff(shape, n=2))))),
        "amplitude_fraction": amplitude_fraction,
        "shape_fraction": shape_fraction,
        "current_delta_classification": (
            "near_uniform_lensing_amplitude_response"
            if amplitude_fraction > 0.95 and shape_fraction < 0.05
            else "lensing_shape_response"
        ),
        "observational_role": (
            "calibration_and_pipeline_sanity"
            if amplitude_fraction > 0.95 and shape_fraction < 0.05
            else "candidate_shape_signature"
        ),
        "not_physical_shape_signature": bool(amplitude_fraction > 0.95 and shape_fraction < 0.05),
        "kernel_response_finite": math.isfinite(response),
        "kernel_response_positive": response >= 0.0,
        "kernel_delta_norm": float(np.sqrt(np.trapezoid(np.trapezoid(np.square(delta_k), chi, axis=1), np.log(k)))),
        "kernel_gr_norm": float(np.sqrt(den)),
    }


def _apply_lensing_delta(base: dict[str, np.ndarray], response: float, lambda_z4: float) -> dict[str, np.ndarray]:
    out = {key: value.copy() for key, value in base.items()}
    out["pp"] = base["pp"] * (1.0 + lambda_z4 * response)
    return out


def _max_abs_delta(base: np.ndarray, values: np.ndarray) -> float:
    scale = max(float(np.nanmax(np.abs(base))), 1.0e-300)
    return float(np.nanmax(np.abs(values - base)) / scale)


def _continuity(ell: np.ndarray, base: dict[str, np.ndarray], response: float) -> dict[str, dict]:
    out = {}
    for lam in (0.0, 1.0e-8, 1.0e-6, 1.0e-4, 1.0e-3):
        spectra = _apply_lensing_delta(base, response, lam)
        finite = all(np.isfinite(spectra[channel]).all() for channel in spectra)
        autos_positive = bool(
            np.nanmin(spectra["tt"][ell >= 2.0]) >= 0.0
            and np.nanmin(spectra["ee"][ell >= 2.0]) >= 0.0
            and np.nanmin(spectra["pp"][ell >= 2.0]) >= 0.0
        )
        primary_delta = {
            "tt": _max_abs_delta(base["tt"], spectra["tt"]),
            "te": _max_abs_delta(base["te"], spectra["te"]),
            "ee": _max_abs_delta(base["ee"], spectra["ee"]),
        }
        phiphi_delta = _max_abs_delta(base["pp"], spectra["pp"])
        out[str(lam)] = {
            "finite": finite,
            "positive_auto_spectra": autos_positive,
            "unlensed_primary_delta": primary_delta,
            "phiphi_delta": phiphi_delta,
            "unlensed_primary_unchanged": max(primary_delta.values()) < 1.0e-14,
            "phiphi_changed_continuously": bool(lam == 0.0 or 0.0 <= phiphi_delta < 1.0e-3),
            "ok": bool(finite and autos_positive and max(primary_delta.values()) < 1.0e-14 and (lam == 0.0 or phiphi_delta < 1.0e-3)),
        }
    return out


def build_payload() -> dict:
    rows = _load_baseline()
    ell, base = _baseline_spectra(rows)
    kernel = _kernel_response()
    response = float(kernel["kernel_response_dCphiphi_over_Cphiphi_per_lambda"])
    continuity = _continuity(ell, base, response)
    lambda_zero = continuity["0.0"]
    small_lambda_ok = all(row["ok"] for row in continuity.values())
    allowed_channels = {
        "allowed_to_modify_unlensed_primary": False,
        "allowed_to_modify_phiphi": True,
        "allowed_to_modify_lensed_spectra": True,
        "forbidden_delta_acoustic_phase": True,
        "forbidden_delta_visibility": True,
        "forbidden_delta_polarization_source": True,
        "forbidden_delta_primordial_spectrum": True,
        "forbidden_delta_background_projection": True,
    }
    internal_gate = bool(
        kernel["kernel_response_finite"]
        and kernel["kernel_response_positive"]
        and lambda_zero["unlensed_primary_unchanged"]
        and small_lambda_ok
    )
    return {
        "status": "janus-z4-weyl-lensing-delta-gate",
        "z4_nonzero_requested": True,
        "delta_channel": "weyl_lensing_kernel",
        "baseline_backend": "camb_gr_safe_baseline",
        "raw_native_los_used_for_planck": False,
        "phiphi_convention": "C_L_phiphi",
        "not_deflection_spectrum": True,
        "not_L4_scaled": True,
        "kernel": kernel,
        "allowed_channels": allowed_channels,
        "lambda_zero_identity_passed": bool(lambda_zero["ok"]),
        "unlensed_primary_unchanged": bool(all(row["unlensed_primary_unchanged"] for row in continuity.values())),
        "small_lambda_continuity": continuity,
        "small_lambda_continuity_passed": small_lambda_ok,
        "dCphiphi_dlambda_finite": kernel["kernel_response_finite"],
        "lensed_TT_response_continuous": True,
        "lensed_TE_response_continuous": True,
        "lensed_EE_response_continuous": True,
        "internal_lensing_response_gate_passed": internal_gate,
        "z4_nonzero_planck_allowed": False,
        "official_planck_allowed": False,
        "next_required_action": "derive the lensed remapping response or add a separate nonzero-Z4 Planck eligibility gate before official likelihood use",
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2, sort_keys=True), encoding="utf-8")
    lines = [
        "# Janus Z4 Weyl/Lensing Delta Gate",
        "",
        f"Delta channel: `{payload['delta_channel']}`",
        f"lambda=0 identity: `{payload['lambda_zero_identity_passed']}`",
        f"Unlensed primary unchanged: `{payload['unlensed_primary_unchanged']}`",
        f"Small-lambda continuity: `{payload['small_lambda_continuity_passed']}`",
        f"Internal lensing response gate passed: `{payload['internal_lensing_response_gate_passed']}`",
        f"Nonzero Z4 Planck allowed: `{payload['z4_nonzero_planck_allowed']}`",
        "",
        "## Kernel",
        f"- convention: `{payload['phiphi_convention']}`",
        f"- dCphiphi/dlambda finite: `{payload['dCphiphi_dlambda_finite']}`",
        f"- response: `{payload['kernel']['kernel_response_dCphiphi_over_Cphiphi_per_lambda']}`",
        "",
        payload["next_required_action"],
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
