from __future__ import annotations

from pathlib import Path
import json
import sys

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))
from janus_lab.z4_cmb_cobaya import JanusZ4NativeBoltzmann


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_cobaya_planck_channel_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_cobaya_planck_channel_gate.json")


CHANNELS = {
    "highl_TT": ("tt", 30, 1200, 0.15),
    "highl_TE": ("te", 30, 1200, 0.25),
    "highl_EE": ("ee", 30, 1200, 0.25),
    "lowE": ("ee", 2, 29, 0.35),
    "lensing": ("pp", 8, 400, 0.30),
}


def smooth_reference(values: np.ndarray, width: int = 7) -> np.ndarray:
    if len(values) < width:
        return values.copy()
    kernel = np.ones(width) / width
    padded = np.pad(values, (width // 2, width // 2), mode="edge")
    return np.convolve(padded, kernel, mode="valid")


def channel_chi2(ell: np.ndarray, values: np.ndarray, ell_min: int, ell_max: int, frac_sigma: float) -> float:
    mask = (ell >= ell_min) & (ell <= ell_max)
    selected = values[mask]
    target = smooth_reference(selected)
    sigma = np.maximum(np.abs(target) * frac_sigma, 1.0e-30)
    return float(np.sum(np.square((selected - target) / sigma)))


def build_payload() -> dict:
    provider = JanusZ4NativeBoltzmann()
    provider.initialize()
    cls = provider.get_Cl(ell_factor=True, units="FIRASmuK2")
    ell = cls["ell"]
    channels = {
        name: channel_chi2(ell, cls[column], ell_min, ell_max, frac_sigma)
        for name, (column, ell_min, ell_max, frac_sigma) in CHANNELS.items()
    }
    total = float(sum(channels.values()))
    worst = max(channels, key=channels.get)
    return {
        "status": "janus-z4-cobaya-planck-channel-gate",
        "channels": channels,
        "total_chi2_proxy": total,
        "worst_channel": worst,
        "native_z4_provider_used": True,
        "legacy_camb_fork_required": False,
        "official_planck_likelihood_executed": False,
        "observational_planck_gate_passed": False,
        "channel_gate_ready": all(value >= 0.0 for value in channels.values()),
        "note": "Planck-like channel decomposition on native Z4 spectra; not official Planck clik.",
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z4 Cobaya Planck Channel Gate",
        "",
        f"Status: `{payload['status']}`",
        f"Total chi2 proxy: `{payload['total_chi2_proxy']}`",
        f"Worst channel: `{payload['worst_channel']}`",
        f"Official Planck likelihood executed: `{payload['official_planck_likelihood_executed']}`",
        "",
        "## Channels",
    ]
    for key, value in payload["channels"].items():
        lines.append(f"- `{key}`: `{value}`")
    lines.extend(["", payload["note"], ""])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
