from __future__ import annotations

from pathlib import Path
import json
import sys

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
sys.path.insert(0, str(ROOT / "src"))

from janus_lab.z4_cmb_cobaya import JanusZ4NativeBoltzmann
from scripts.build_p0_eft_janus_z4_shape_diagnostic import best_amplitude, planck_shape_reference


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_peak_damping_diagnostic.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_peak_damping_diagnostic.json")


def _local_maxima(ell: np.ndarray, values: np.ndarray, ell_min: int, ell_max: int) -> list[dict]:
    mask = (ell >= ell_min) & (ell <= ell_max)
    e = ell[mask]
    v = values[mask]
    peaks: list[dict] = []
    for idx in range(1, len(e) - 1):
        if v[idx] >= v[idx - 1] and v[idx] >= v[idx + 1]:
            peaks.append({"ell": int(e[idx]), "value": float(v[idx])})
    return sorted(peaks, key=lambda item: item["value"], reverse=True)


def _zero_crossings(ell: np.ndarray, values: np.ndarray, ell_min: int, ell_max: int) -> list[float]:
    mask = (ell >= ell_min) & (ell <= ell_max)
    e = ell[mask].astype(float)
    v = values[mask].astype(float)
    crossings: list[float] = []
    for idx in range(len(e) - 1):
        if v[idx] == 0.0:
            crossings.append(float(e[idx]))
        elif v[idx] * v[idx + 1] < 0.0:
            frac = abs(v[idx]) / (abs(v[idx]) + abs(v[idx + 1]))
            crossings.append(float(e[idx] + frac * (e[idx + 1] - e[idx])))
    return crossings


def _damping_slope(ell: np.ndarray, values: np.ndarray, ell_min: int, ell_max: int) -> float:
    mask = (ell >= ell_min) & (ell <= ell_max) & (values > 0.0)
    e = ell[mask].astype(float)
    v = values[mask].astype(float)
    if len(e) < 3:
        return float("nan")
    slope, _ = np.polyfit(e, np.log(v), 1)
    return float(slope)


def _peak_block(ell: np.ndarray, model: np.ndarray, channel: str, ell_min: int, ell_max: int) -> dict:
    ref = planck_shape_reference(ell, channel)
    sigma = np.maximum(np.abs(ref) * 0.18, np.nanmax(np.abs(ref)) * 0.015 + 1.0e-30)
    amp = best_amplitude(model, ref, sigma)
    model_scaled = amp * model
    model_peaks = _local_maxima(ell, model_scaled, ell_min, ell_max)[:5]
    ref_peaks = _local_maxima(ell, ref, ell_min, ell_max)[:5]
    paired = []
    for lhs, rhs in zip(model_peaks, ref_peaks):
        paired.append(
            {
                "model_ell": lhs["ell"],
                "reference_ell": rhs["ell"],
                "ell_shift": int(lhs["ell"] - rhs["ell"]),
                "amplitude_ratio": float(lhs["value"] / rhs["value"]) if rhs["value"] else float("nan"),
            }
        )
    return {
        "channel": channel,
        "ell_min": ell_min,
        "ell_max": ell_max,
        "best_shape_amplitude": amp,
        "paired_peaks": paired,
    }


def build_payload() -> dict:
    provider = JanusZ4NativeBoltzmann()
    provider.initialize()
    cls = provider.get_Cl(ell_factor=True, units="FIRASmuK2")
    ell = cls["ell"]

    tt_peak_block = _peak_block(ell, cls["tt"], "tt", 30, 900)
    ee_peak_block = _peak_block(ell, cls["ee"], "ee", 30, 1200)

    te_ref = planck_shape_reference(ell, "te")
    te_amp = best_amplitude(cls["te"], te_ref, np.maximum(np.abs(te_ref) * 0.18, 1.0))
    te_model_crossings = _zero_crossings(ell, te_amp * cls["te"], 30, 1200)[:8]
    te_ref_crossings = _zero_crossings(ell, te_ref, 30, 1200)[:8]
    te_phase = [
        {
            "model_zero_ell": float(lhs),
            "reference_zero_ell": float(rhs),
            "ell_shift": float(lhs - rhs),
        }
        for lhs, rhs in zip(te_model_crossings, te_ref_crossings)
    ]

    tt_ref = planck_shape_reference(ell, "tt")
    tt_amp = best_amplitude(cls["tt"], tt_ref, np.maximum(np.abs(tt_ref) * 0.18, 1.0))
    damping = {
        "model_log_slope": _damping_slope(ell, tt_amp * cls["tt"], 900, 1800),
        "reference_log_slope": _damping_slope(ell, tt_ref, 900, 1800),
    }
    damping["slope_residual"] = float(damping["model_log_slope"] - damping["reference_log_slope"])

    max_tt_shift = max((abs(item["ell_shift"]) for item in tt_peak_block["paired_peaks"]), default=0)
    max_te_shift = max((abs(item["ell_shift"]) for item in te_phase), default=0.0)
    return {
        "status": "janus-z4-peak-damping-diagnostic",
        "native_z4_provider_used": True,
        "compressed_lcdm_parameters_used": False,
        "official_planck_likelihood_executed": False,
        "tt_peak_phase": tt_peak_block,
        "ee_peak_phase": ee_peak_block,
        "te_zero_phase": te_phase,
        "te_zero_crossings_found": bool(te_phase),
        "tt_damping_slope": damping,
        "max_tt_peak_shift": float(max_tt_shift),
        "max_te_zero_shift": float(max_te_shift),
        "peak_damping_diagnostic_ready": True,
        "cmb_engine_physically_closed": False,
        "verdict": (
            "Native Z4 has a usable diagnostic spectrum, but acoustic phase/source "
            "closure remains incomplete: peak shifts, TE zero-phase residuals and "
            "TT damping slope residuals are explicitly exposed. Missing TE zero "
            "crossings are treated as a source-phase failure."
        ),
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z4 Peak/Damping Diagnostic",
        "",
        f"Status: `{payload['status']}`",
        f"CMB engine physically closed: `{payload['cmb_engine_physically_closed']}`",
        f"Max TT peak shift: `{payload['max_tt_peak_shift']:.6g}`",
        f"Max TE zero shift: `{payload['max_te_zero_shift']:.6g}`",
        f"TE zero crossings found: `{payload['te_zero_crossings_found']}`",
        f"TT damping slope residual: `{payload['tt_damping_slope']['slope_residual']:.6g}`",
        "",
        "## TT paired peaks",
    ]
    for item in payload["tt_peak_phase"]["paired_peaks"]:
        lines.append(
            f"- model ell `{item['model_ell']}`, ref ell `{item['reference_ell']}`, "
            f"shift `{item['ell_shift']}`, amp ratio `{item['amplitude_ratio']:.6g}`"
        )
    lines.extend(["", "## TE zero crossings"])
    for item in payload["te_zero_phase"]:
        lines.append(
            f"- model ell `{item['model_zero_ell']:.6g}`, ref ell `{item['reference_zero_ell']:.6g}`, "
            f"shift `{item['ell_shift']:.6g}`"
        )
    lines.extend(["", payload["verdict"], ""])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
