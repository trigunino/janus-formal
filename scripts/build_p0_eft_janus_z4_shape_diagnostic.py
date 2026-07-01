from __future__ import annotations

from pathlib import Path
import json

import numpy as np

import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))
from janus_lab.z4_cmb_cobaya import JanusZ4NativeBoltzmann


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_shape_diagnostic.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_shape_diagnostic.json")

BANDS = {
    "lowTT": ("tt", 2, 29),
    "lowE": ("ee", 2, 29),
    "highl_TT_peak1": ("tt", 30, 450),
    "highl_TT_damping": ("tt", 900, 1800),
    "highl_TE": ("te", 30, 1200),
    "highl_EE": ("ee", 30, 1200),
    "lensing": ("pp", 8, 400),
}


def planck_shape_reference(ell: np.ndarray, channel: str) -> np.ndarray:
    x = np.maximum(ell, 2.0)
    if channel == "tt":
        envelope = 5600.0 * np.exp(-np.square(x / 1850.0)) / np.power(x / 220.0, 0.06)
        peaks = 1.0 + 0.46 * np.cos((x - 220.0) / 112.0 * np.pi) * np.exp(-x / 2600.0)
        return np.maximum(envelope * peaks, 1.0)
    if channel == "ee":
        envelope = 14.0 * np.power(x / 420.0, 0.75) * np.exp(-np.square(x / 1950.0))
        peaks = 1.0 - 0.55 * np.cos((x - 390.0) / 105.0 * np.pi) * np.exp(-x / 2800.0)
        return np.maximum(envelope * peaks, 1.0e-4)
    if channel == "te":
        envelope = 115.0 * np.exp(-np.square(x / 1850.0))
        return envelope * np.sin((x - 90.0) / 108.0 * np.pi)
    if channel == "pp":
        return 2.0e-7 / np.power(x + 20.0, 1.15) * np.exp(-x / 700.0)
    raise ValueError(channel)


def best_amplitude(model: np.ndarray, ref: np.ndarray, sigma: np.ndarray) -> float:
    denom = float(np.sum(np.square(model / sigma)))
    if denom <= 0.0:
        return 1.0
    return float(np.sum(model * ref / np.square(sigma)) / denom)


def band_score(ell: np.ndarray, values: np.ndarray, channel: str, ell_min: int, ell_max: int) -> dict:
    mask = (ell >= ell_min) & (ell <= ell_max)
    e = ell[mask]
    v = values[mask]
    ref = planck_shape_reference(e, channel)
    sigma = np.maximum(np.abs(ref) * 0.18, np.nanmax(np.abs(ref)) * 0.015 + 1.0e-30)
    amp = best_amplitude(v, ref, sigma)
    residual = amp * v - ref
    pulls = residual / sigma
    idx = int(np.argmax(np.abs(pulls))) if len(pulls) else 0
    top_indices = np.argsort(np.abs(pulls))[-3:][::-1] if len(pulls) else []
    chi2 = float(np.sum(np.square(pulls)))
    dof = max(int(len(e) - 1), 1)
    return {
        "channel": channel,
        "ell_min": ell_min,
        "ell_max": ell_max,
        "points": int(len(e)),
        "best_shape_amplitude": amp,
        "chi2_shape": chi2,
        "chi2_per_dof": chi2 / dof,
        "max_abs_pull": float(abs(pulls[idx])) if len(pulls) else 0.0,
        "max_pull_ell": int(e[idx]) if len(e) else None,
        "dominant_pulls": [
            {
                "ell": int(e[item]),
                "pull": float(pulls[item]),
                "model": float(amp * v[item]),
                "reference": float(ref[item]),
            }
            for item in top_indices
        ],
    }


def build_payload() -> dict:
    provider = JanusZ4NativeBoltzmann()
    provider.initialize()
    cls = provider.get_Cl(ell_factor=True, units="FIRASmuK2")
    ell = cls["ell"]
    bands = {
        name: band_score(ell, cls[channel], channel, ell_min, ell_max)
        for name, (channel, ell_min, ell_max) in BANDS.items()
    }
    worst = max(bands, key=lambda key: bands[key]["chi2_per_dof"])
    return {
        "status": "janus-z4-shape-diagnostic",
        "native_z4_provider_used": True,
        "compressed_lcdm_parameters_used": False,
        "official_planck_likelihood_executed": False,
        "bands": bands,
        "worst_band": worst,
        "shape_diagnostic_ready": True,
        "note": "Shape-only public-form diagnostic; not a Planck best-fit validation and not a substitute for clik.",
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z4 Shape Diagnostic",
        "",
        f"Status: `{payload['status']}`",
        f"Worst band: `{payload['worst_band']}`",
        f"Compressed LCDM parameters used: `{payload['compressed_lcdm_parameters_used']}`",
        "",
        "## Bands",
    ]
    for name, band in payload["bands"].items():
        lines.append(
            f"- `{name}`: chi2/dof `{band['chi2_per_dof']:.6g}`, "
            f"max pull `{band['max_abs_pull']:.6g}` at ell `{band['max_pull_ell']}`"
        )
        for pull in band["dominant_pulls"]:
            lines.append(
                f"  - ell `{pull['ell']}` pull `{pull['pull']:.6g}` "
                f"model `{pull['model']:.6g}` ref `{pull['reference']:.6g}`"
            )
    lines.extend(["", payload["note"], ""])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
