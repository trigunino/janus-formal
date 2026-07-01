from __future__ import annotations

from pathlib import Path
import json
import math
import re
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from scripts.run_p0_eft_coherent_primordial_immirzi_planck_gate import (
    SOURCE_PATH,
    build_fork,
    reference_chi2,
    run_cobaya,
)
from scripts.run_p0_eft_predrag_background_only_geff_scan import target_delta_i


REPORT_PATH = Path("outputs/reports/p0_eft_screened_geff_camb_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_screened_geff_camb_gate.json")
SOUND_TARGET_PATH = Path("outputs/reports/p0_eft_sound_horizon_global_integral.json")

A_CENTER = 1.0e-4
WIDTH = 5.0e-5
SCREENING = 0.1


def replace_param(text: str, param_name: str, value: float, count: int = 0) -> str:
    pattern = rf"(real\(dl\), parameter :: {re.escape(param_name)} = )[-+0-9.eE]+_dl"
    return re.sub(pattern, rf"\g<1>{value:.16e}_dl", text, count=count)


def required_rd_ratio() -> float:
    return float(json.loads(SOUND_TARGET_PATH.read_text(encoding="utf-8"))["required_rd_ratio_from_bao"])


def set_screened_profile(c_background: float, c_cmb: float) -> None:
    text = SOURCE_PATH.read_text(encoding="utf-8")
    text = replace_param(text, "a_drag", A_CENTER)
    text = replace_param(text, "width", WIDTH, count=1)
    text = replace_param(text, "c_geff", 0.0)
    text = replace_param(text, "c_geff_background", c_background)
    text = replace_param(text, "c_geff_cmb", c_cmb)
    text = replace_param(text, "c_immirzi", 0.0)
    text = replace_param(text, "c_coherent_immirzi", 0.0)
    text = replace_param(text, "c_sound", 0.0)
    text = replace_param(text, "c_opacity", 0.0)
    SOURCE_PATH.write_text(text, encoding="utf-8")


def build_payload(execute: bool = True) -> dict:
    c_background = target_delta_i()
    c_cmb = SCREENING * c_background
    rd_ratio = 1.0 / math.sqrt(1.0 + c_background)
    point = {
        "screening": SCREENING,
        "c_background": c_background,
        "c_cmb": c_cmb,
        "a_center": A_CENTER,
        "width": WIDTH,
        "rd_ratio_background": rd_ratio,
        "required_rd_ratio": required_rd_ratio(),
    }
    if not execute:
        return {
            "description": "Real CAMB fork gate with split background and screened perturbative G_eff hooks.",
            "status": "screened-geff-camb-gate-dry",
            "point": point,
            "full_cosmology_prediction_ready_no_fit": False,
        }

    ref = reference_chi2()
    original = SOURCE_PATH.read_text(encoding="utf-8")
    try:
        set_screened_profile(c_background, c_cmb)
        build_code = build_fork()
        result = run_cobaya() if build_code == 0 else {"returncode": build_code, "chi2_CMB": None}
    finally:
        SOURCE_PATH.write_text(original, encoding="utf-8")
        build_fork()

    deltas = {
        f"delta_{key}": result[key] - ref[key]
        for key in ref
        if result.get(key) is not None
    }
    return {
        "description": "Real CAMB fork gate with split background and screened perturbative G_eff hooks.",
        "status": "screened-geff-camb-gate-run",
        "point": point,
        "result": {**result, **deltas, "build_returncode": build_code},
        "rd_window_hit": abs(rd_ratio - point["required_rd_ratio"]) < 0.005,
        "planck_improves": bool(deltas.get("delta_chi2_CMB", 1.0) < 0.0),
        "screened_hook_is_effective": bool(abs(c_cmb - c_background) > 1e-12),
        "full_cosmology_prediction_ready_no_fit": False,
        "next_required": "If this passes, derive the screening factor; if it fails, the mono-metric CAMB EFT hook is still insufficient.",
    }


def render_markdown(payload: dict) -> str:
    point = payload["point"]
    result = payload.get("result", {})
    return "\n".join(
        [
            "# P0 EFT Screened G_eff CAMB Gate",
            "",
            payload["description"],
            "",
            f"Status: `{payload['status']}`",
            f"c_background: `{point['c_background']}`",
            f"c_cmb: `{point['c_cmb']}`",
            f"screening: `{point['screening']}`",
            f"r_d background ratio: `{point['rd_ratio_background']}`",
            f"required r_d ratio: `{point['required_rd_ratio']}`",
            f"rd window hit: `{payload.get('rd_window_hit')}`",
            f"planck improves: `{payload.get('planck_improves')}`",
            f"chi2 CMB: `{result.get('chi2_CMB')}`",
            f"delta chi2 CMB: `{result.get('delta_chi2_CMB')}`",
            f"delta highl: `{result.get('delta_chi2_highl')}`",
            f"delta lensing: `{result.get('delta_chi2_lensing')}`",
            "",
            payload.get("next_required", ""),
            "",
        ]
    )


def write_reports(execute: bool = True) -> dict:
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    payload = build_payload(execute=execute)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(render_markdown(payload), encoding="utf-8")
    return payload


def main() -> None:
    write_reports()
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {JSON_PATH}")


if __name__ == "__main__":
    main()
