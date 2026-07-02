from __future__ import annotations

import json
import math
import sys
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))
    sys.path.insert(0, str(ROOT / "src"))

from janus_lab.z4_cmb_solver import Z4CMBSolverSettings, solve_z4_cmb
from janus_lab.z4_regenerative_camb_provider import CosmologyPoint, generate_camb_gr_rows

REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_complete_gr_limit_shape_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_complete_gr_limit_shape_gate.json")


def _scale(raw: np.ndarray, reference: np.ndarray) -> float:
    denom = float(np.dot(raw, raw))
    return 0.0 if denom == 0.0 else float(np.dot(raw, reference) / denom)


def _channel_metrics(raw: list[float], reference: list[float]) -> dict:
    r = np.asarray(raw, dtype=float)
    y = np.asarray(reference, dtype=float)
    scale = _scale(r, y)
    calibrated = scale * r
    denom = float(np.linalg.norm(y))
    rms = float(np.linalg.norm(calibrated - y) / denom) if denom > 0.0 else math.inf
    mask = np.abs(y) > max(1.0e-30, 1.0e-3 * float(np.max(np.abs(y))))
    frac = np.abs(calibrated[mask] / y[mask] - 1.0) if np.any(mask) else np.asarray([math.inf])
    sign_mask = mask & (np.abs(calibrated) > 1.0e-30)
    sign_agreement = float(np.mean(np.sign(calibrated[sign_mask]) == np.sign(y[sign_mask]))) if np.any(sign_mask) else 0.0
    return {
        "calibration_scale": scale,
        "relative_rms": rms,
        "max_fractional_residual": float(np.max(frac)),
        "sign_agreement": sign_agreement,
    }


def build_payload() -> dict:
    settings = Z4CMBSolverSettings(z4_enabled=False)
    solver = solve_z4_cmb(CosmologyPoint(), settings)
    ells = [int(row["ell"]) for row in solver["lensed_spectra"]]
    reference_rows = generate_camb_gr_rows(CosmologyPoint(), ells=ells)
    native = {
        "cl_tt": [row["cl_tt_lensed_proxy"] for row in solver["lensed_spectra"]],
        "cl_te": [row["cl_te_lensed_proxy"] for row in solver["lensed_spectra"]],
        "cl_ee": [row["cl_ee_lensed_proxy"] for row in solver["lensed_spectra"]],
        "cl_phiphi": [row["cl_phiphi"] for row in solver["cl_phiphi"]],
    }
    reference = {
        "cl_tt": [row["cl_tt"] for row in reference_rows],
        "cl_te": [row["cl_te"] for row in reference_rows],
        "cl_ee": [row["cl_ee"] for row in reference_rows],
        "cl_phiphi": [row["cl_pp"] for row in reference_rows],
    }
    metrics = {channel: _channel_metrics(native[channel], reference[channel]) for channel in native}
    channel_pass = {
        "cl_tt": metrics["cl_tt"]["relative_rms"] < 0.25 and metrics["cl_tt"]["max_fractional_residual"] < 1.0,
        "cl_te": metrics["cl_te"]["relative_rms"] < 0.5 and metrics["cl_te"]["sign_agreement"] > 0.75,
        "cl_ee": metrics["cl_ee"]["relative_rms"] < 0.35 and metrics["cl_ee"]["max_fractional_residual"] < 1.5,
        "cl_phiphi": metrics["cl_phiphi"]["relative_rms"] < 0.5 and metrics["cl_phiphi"]["max_fractional_residual"] < 2.0,
    }
    passed = bool(all(channel_pass.values()))
    return {
        "status": "janus-z4-complete-gr-limit-shape-gate",
        "z4_enabled": False,
        "gr_limit_backend": solver["provenance"].get("gr_limit_backend", "native_proxy"),
        "native_gr_limit_solver_executed": True,
        "camb_gr_reference_generated": True,
        "ell": ells,
        "channel_metrics": metrics,
        "channel_pass": channel_pass,
        "gr_limit_shape_passed": passed,
        "z4_on_planck_interpretation_allowed": passed,
        "observed_planck_validation": False,
        "candidate_promotion_allowed": False,
        "full_planck_validation": False,
        "failure_interpretation": "native_gr_limit_shape_mismatch" if not passed else "none",
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z4 Complete GR-Limit Shape Gate",
        "",
        f"GR-limit shape passed: `{payload['gr_limit_shape_passed']}`",
        f"Z4-on Planck interpretation allowed: `{payload['z4_on_planck_interpretation_allowed']}`",
        "",
    ]
    for channel, metrics in payload["channel_metrics"].items():
        lines.append(
            f"- `{channel}`: rms=`{metrics['relative_rms']:.6g}`, "
            f"max_frac=`{metrics['max_fractional_residual']:.6g}`, "
            f"sign=`{metrics['sign_agreement']:.3f}`"
        )
    REPORT_PATH.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
