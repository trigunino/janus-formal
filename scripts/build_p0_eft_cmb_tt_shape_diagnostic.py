from __future__ import annotations

from pathlib import Path
import csv
import json
import os
import sys

import numpy as np

REPORT_PATH = Path("outputs/reports/p0_eft_cmb_tt_shape_diagnostic.md")
JSON_PATH = Path("outputs/reports/p0_eft_cmb_tt_shape_diagnostic.json")
CSV_PATH = Path("outputs/reports/p0_eft_cmb_tt_shape_diagnostic.csv")
FORK_PATH = Path("external/camb_janus_fork").resolve()

PARAMS = {
    "H0": 67.4,
    "ombh2": 0.0224,
    "omch2": 0.136,
    "As": 2.1e-9,
    "ns": 0.94,
    "tau": 0.035,
    "nnu": 3.7424238,
    "YHe": 0.245,
}


def winget_gfortran_bin() -> str | None:
    root = Path(os.environ.get("LOCALAPPDATA", "")) / "Microsoft/WinGet/Packages"
    matches = list(root.rglob("gfortran.exe")) if root.exists() else []
    return str(matches[0].parent) if matches else None


def camb_cls(camb_module, lmax: int = 1800) -> np.ndarray:
    pars = camb_module.CAMBparams()
    pars.set_cosmology(
        H0=PARAMS["H0"],
        ombh2=PARAMS["ombh2"],
        omch2=PARAMS["omch2"],
        tau=PARAMS["tau"],
        nnu=PARAMS["nnu"],
        YHe=PARAMS["YHe"],
        mnu=0.06,
        omk=0.0,
    )
    pars.InitPower.set_params(As=PARAMS["As"], ns=PARAMS["ns"])
    pars.set_for_lmax(lmax, lens_potential_accuracy=1)
    results = camb_module.get_results(pars)
    return results.get_cmb_power_spectra(pars, CMB_unit="muK")["total"][: lmax + 1]


def import_fork_camb():
    for name in list(sys.modules):
        if name == "camb" or name.startswith("camb."):
            sys.modules.pop(name, None)
    bin_dir = winget_gfortran_bin()
    if bin_dir:
        os.environ["PATH"] = bin_dir + os.pathsep + os.environ.get("PATH", "")
    sys.path.insert(0, str(FORK_PATH))
    import camb

    del sys.path[0]
    return camb


def import_stock_camb():
    for name in list(sys.modules):
        if name == "camb" or name.startswith("camb."):
            sys.modules.pop(name, None)
    import camb

    return camb


def peak_ell(tt: np.ndarray, lo: int, hi: int) -> int:
    segment = tt[lo : hi + 1]
    return int(lo + np.argmax(segment))


def band_mean(values: np.ndarray, lo: int, hi: int) -> float:
    return float(np.mean(values[lo : hi + 1]))


def build_payload() -> dict:
    fork_camb = import_fork_camb()
    fork_file = str(Path(fork_camb.__file__).resolve())
    fork = camb_cls(fork_camb)
    stock_camb = import_stock_camb()
    stock_file = str(Path(stock_camb.__file__).resolve())
    stock = camb_cls(stock_camb)

    ell = np.arange(len(stock))
    stock_tt = stock[:, 0]
    fork_tt = fork[:, 0]
    ratio = np.divide(fork_tt, stock_tt, out=np.ones_like(fork_tt), where=stock_tt != 0)

    CSV_PATH.parent.mkdir(parents=True, exist_ok=True)
    with CSV_PATH.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.writer(handle)
        writer.writerow(["ell", "TT_stock", "TT_fork", "ratio"])
        for i in range(2, len(stock_tt)):
            writer.writerow([i, stock_tt[i], fork_tt[i], ratio[i]])

    low_ratio = band_mean(ratio, 30, 300)
    mid_ratio = band_mean(ratio, 300, 900)
    high_ratio = band_mean(ratio, 900, 1600)
    tilt_proxy = high_ratio / mid_ratio if mid_ratio else None
    stock_peak1 = peak_ell(stock_tt, 100, 350)
    fork_peak1 = peak_ell(fork_tt, 100, 350)
    stock_peak2 = peak_ell(stock_tt, 350, 700)
    fork_peak2 = peak_ell(fork_tt, 350, 700)

    return {
        "description": "TT shape diagnostic comparing stock CAMB and Janus-patched CAMB fork at the current best CMB point.",
        "status": "tt-shape-diagnostic-run",
        "stock_camb_file": stock_file,
        "fork_camb_file": fork_file,
        "fork_loaded": str(FORK_PATH).lower() in fork_file.lower(),
        "csv": str(CSV_PATH),
        "band_ratios": {
            "low_ell_30_300": low_ratio,
            "mid_ell_300_900": mid_ratio,
            "high_ell_900_1600": high_ratio,
            "high_over_mid_tilt_proxy": tilt_proxy,
        },
        "peaks": {
            "stock_peak1_ell": stock_peak1,
            "fork_peak1_ell": fork_peak1,
            "peak1_shift": fork_peak1 - stock_peak1,
            "stock_peak2_ell": stock_peak2,
            "fork_peak2_ell": fork_peak2,
            "peak2_shift": fork_peak2 - stock_peak2,
        },
        "next_required": "If ratios are near one, Planck rejection is driven by absolute cosmological/nuisance calibration; otherwise inspect Janus Weyl hook shape.",
    }


def render_markdown(payload: dict) -> str:
    bands = payload["band_ratios"]
    peaks = payload["peaks"]
    return "\n".join(
        [
            "# P0 EFT CMB TT Shape Diagnostic",
            "",
            payload["description"],
            "",
            f"Status: {payload['status']}",
            f"Fork loaded: {payload['fork_loaded']}",
            "",
            "## Band Ratios fork/stock",
            "",
            f"- ell 30-300: `{bands['low_ell_30_300']}`",
            f"- ell 300-900: `{bands['mid_ell_300_900']}`",
            f"- ell 900-1600: `{bands['high_ell_900_1600']}`",
            f"- high/mid tilt proxy: `{bands['high_over_mid_tilt_proxy']}`",
            "",
            "## Peak Shifts",
            "",
            f"- peak 1 shift: `{peaks['peak1_shift']}`",
            f"- peak 2 shift: `{peaks['peak2_shift']}`",
            "",
            "## Next",
            "",
            payload["next_required"],
            "",
        ]
    )


def write_reports(report_path: Path = REPORT_PATH, json_path: Path = JSON_PATH) -> dict:
    report_path.parent.mkdir(parents=True, exist_ok=True)
    payload = build_payload()
    json_path.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    report_path.write_text(render_markdown(payload), encoding="utf-8")
    return payload


def main() -> None:
    write_reports()
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {JSON_PATH}")
    print(f"Wrote {CSV_PATH}")


if __name__ == "__main__":
    main()
