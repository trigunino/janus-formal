from __future__ import annotations

from pathlib import Path
import json
import math
import sys

from cobaya.model import get_model

REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_lensing_amplitude_diagnostic.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_lensing_amplitude_diagnostic.json")
SCALES = [1.0e-4, 1.0e-3, 1.0e-2, 1.0e-1, 1.0, 10.0, 100.0]


def run_lensing(scale: float) -> dict:
    sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))
    info = {
        "theory": {
            "janus_lab.z4_cmb_cobaya.JanusZ4NativeBoltzmann": {
                "pp_calibration_target": 1.0e-7 * scale,
            }
        },
        "likelihood": {"planck_2018_lensing.clik": None},
        "params": {"janus_dummy": {"value": 0.0}, "A_planck": {"value": 1.0}},
        "packages_path": "external/cobaya_packages",
        "stop_at_error": False,
    }
    try:
        model = get_model(info)
        loglikes, _derived = model.loglikes({"janus_dummy": 0.0}, return_derived=True)
        loglike = float(loglikes[0])
        chi2 = -2.0 * loglike if math.isfinite(loglike) else math.inf
        return {"scale": scale, "executed": True, "chi2": chi2, "finite": math.isfinite(chi2), "error": None}
    except Exception as exc:  # pragma: no cover - audit path
        return {"scale": scale, "executed": False, "chi2": None, "finite": False, "error": f"{type(exc).__name__}: {exc}"}


def build_payload() -> dict:
    rows = [run_lensing(scale) for scale in SCALES]
    finite = [row for row in rows if row["finite"]]
    best = min(finite, key=lambda row: row["chi2"]) if finite else None
    return {
        "status": "janus-z4-lensing-amplitude-diagnostic",
        "native_z4_spectra_used": True,
        "official_planck_lensing_executed": any(row["executed"] for row in rows),
        "compressed_lcdm_parameters_used": False,
        "rows": rows,
        "best": best,
        "amplitude_only_sufficient": bool(best and best["chi2"] < 100.0),
    }


def write_reports() -> dict:
    payload = build_payload()
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z4 Lensing Amplitude Diagnostic",
        "",
        f"Best: `{payload['best']}`",
        f"Amplitude-only sufficient: `{payload['amplitude_only_sufficient']}`",
        "",
        "## Rows",
    ]
    for row in payload["rows"]:
        lines.append(f"- scale `{row['scale']}` chi2 `{row['chi2']}` error `{row['error']}`")
    REPORT_PATH.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
