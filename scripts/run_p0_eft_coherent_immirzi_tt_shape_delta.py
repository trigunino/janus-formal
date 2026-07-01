from __future__ import annotations

from pathlib import Path
import csv
import json
import os
import subprocess
import sys
import tempfile

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from scripts.run_p0_eft_coherent_primordial_immirzi_planck_gate import (
    FORK_PATH,
    SOURCE_PATH,
    delta_i,
    set_coherent_immirzi,
    build_fork,
    winget_gfortran_bin,
)


REPORT_PATH = Path("outputs/reports/p0_eft_coherent_immirzi_tt_shape_delta.md")
JSON_PATH = Path("outputs/reports/p0_eft_coherent_immirzi_tt_shape_delta.json")
CSV_PATH = Path("outputs/reports/p0_eft_coherent_immirzi_tt_shape_delta.csv")

PARAMS = {
    "H0": 67.4,
    "ombh2": 0.02237,
    "omch2": 0.136,
    "tau": 0.054,
    "As": 2.1e-9,
    "ns": 0.965,
    "nnu": 3.7424238,
}


def cls_tt(lmax: int = 2200) -> np.ndarray:
    with tempfile.NamedTemporaryFile(suffix=".npy", delete=False) as handle:
        out_path = Path(handle.name)
    code = f"""
import numpy as np, sys
sys.path.insert(0, r'{FORK_PATH}')
import camb
pars = camb.CAMBparams()
pars.set_cosmology(H0={PARAMS['H0']}, ombh2={PARAMS['ombh2']}, omch2={PARAMS['omch2']}, tau={PARAMS['tau']}, nnu={PARAMS['nnu']}, YHe=0.245, mnu=0.06, omk=0.0)
pars.InitPower.set_params(As={PARAMS['As']}, ns={PARAMS['ns']})
pars.set_for_lmax({lmax}, lens_potential_accuracy=1)
results = camb.get_results(pars)
np.save(r'{out_path}', results.get_cmb_power_spectra(pars, CMB_unit='muK')['total'][:{lmax + 1}, 0])
"""
    env = os.environ.copy()
    bin_dir = winget_gfortran_bin()
    if bin_dir:
        env["PATH"] = bin_dir + os.pathsep + env.get("PATH", "")
    result = subprocess.run([sys.executable, "-c", code], text=True, capture_output=True, env=env, check=False)
    if result.returncode != 0:
        raise RuntimeError(result.stdout + result.stderr)
    try:
        return np.load(out_path)
    finally:
        out_path.unlink(missing_ok=True)


def band_mean(values: np.ndarray, lo: int, hi: int) -> float:
    return float(np.mean(values[lo : hi + 1]))


def peak_ell(tt: np.ndarray, lo: int, hi: int) -> int:
    return int(lo + np.argmax(tt[lo : hi + 1]))


def compute(execute: bool = True) -> dict:
    value = delta_i()
    if not execute:
        return {"status": "coherent-immirzi-tt-shape-delta-dry", "c_coherent_immirzi": value}
    original = SOURCE_PATH.read_text(encoding="utf-8")
    try:
        set_coherent_immirzi(0.0)
        build_fork()
        neutral = cls_tt()
        set_coherent_immirzi(value)
        build_fork()
        active = cls_tt()
    finally:
        SOURCE_PATH.write_text(original, encoding="utf-8")
        build_fork()

    ratio = np.divide(active, neutral, out=np.ones_like(active), where=neutral != 0)
    CSV_PATH.parent.mkdir(parents=True, exist_ok=True)
    with CSV_PATH.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.writer(handle)
        writer.writerow(["ell", "TT_neutral", "TT_active", "ratio"])
        for ell in range(2, len(ratio)):
            writer.writerow([ell, neutral[ell], active[ell], ratio[ell]])

    neutral_peak1 = peak_ell(neutral, 100, 350)
    active_peak1 = peak_ell(active, 100, 350)
    neutral_peak2 = peak_ell(neutral, 350, 700)
    active_peak2 = peak_ell(active, 350, 700)
    return {
        "description": "TT shape delta for coherent Holst-Immirzi stress tensor: active versus neutral fork at fixed Janus point.",
        "status": "coherent-immirzi-tt-shape-delta-run",
        "c_coherent_immirzi": value,
        "band_ratios": {
            "low_30_300": band_mean(ratio, 30, 300),
            "mid_300_900": band_mean(ratio, 300, 900),
            "high_900_1600": band_mean(ratio, 900, 1600),
            "damping_proxy_high_over_mid": band_mean(ratio, 900, 1600) / band_mean(ratio, 300, 900),
        },
        "peak_shifts": {
            "peak1": active_peak1 - neutral_peak1,
            "peak2": active_peak2 - neutral_peak2,
        },
        "csv": str(CSV_PATH),
        "next_required": "If peak shifts are near zero but high/mid changes, residual is damping/amplitude; if shifts are nonzero, derive sound-horizon phase correction.",
    }


def render_markdown(payload: dict) -> str:
    bands = payload.get("band_ratios", {})
    peaks = payload.get("peak_shifts", {})
    return "\n".join(
        [
            "# P0 EFT Coherent Immirzi TT Shape Delta",
            "",
            payload.get("description", ""),
            "",
            f"Status: `{payload['status']}`",
            f"c_coherent_immirzi: `{payload['c_coherent_immirzi']}`",
            "",
            "## Ratios active/neutral",
            "",
            f"- low 30-300: `{bands.get('low_30_300')}`",
            f"- mid 300-900: `{bands.get('mid_300_900')}`",
            f"- high 900-1600: `{bands.get('high_900_1600')}`",
            f"- damping high/mid: `{bands.get('damping_proxy_high_over_mid')}`",
            "",
            "## Peak Shifts",
            "",
            f"- peak1: `{peaks.get('peak1')}`",
            f"- peak2: `{peaks.get('peak2')}`",
            "",
            payload.get("next_required", ""),
            "",
        ]
    )


def write_reports(execute: bool = True) -> dict:
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    payload = compute(execute=execute)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(render_markdown(payload), encoding="utf-8")
    return payload


def main() -> None:
    write_reports()
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {JSON_PATH}")
    print(f"Wrote {CSV_PATH}")


if __name__ == "__main__":
    main()
