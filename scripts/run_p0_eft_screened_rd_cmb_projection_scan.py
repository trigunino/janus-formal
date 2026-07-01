from __future__ import annotations

from pathlib import Path
import json
import math
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from scripts.run_p0_eft_predrag_background_only_geff_scan import (
    set_profile_and_geff,
    target_delta_i,
)
from scripts.run_p0_eft_coherent_primordial_immirzi_planck_gate import (
    SOURCE_PATH,
    build_fork,
    run_cobaya,
    reference_chi2,
)


REPORT_PATH = Path("outputs/reports/p0_eft_screened_rd_cmb_projection_scan.md")
JSON_PATH = Path("outputs/reports/p0_eft_screened_rd_cmb_projection_scan.json")
CSV_PATH = Path("outputs/reports/p0_eft_screened_rd_cmb_projection_scan.csv")
SOUND_TARGET_PATH = Path("outputs/reports/p0_eft_sound_horizon_global_integral.json")

SCREEN_GRID = [0.0, 0.1, 0.2, 0.3, 1.0 / 3.0, 0.4, 0.5]
A_CENTER = 1.0e-4
WIDTH = 5.0e-5


def required_rd_ratio() -> float:
    return float(json.loads(SOUND_TARGET_PATH.read_text(encoding="utf-8"))["required_rd_ratio_from_bao"])


def build_payload(execute: bool = True) -> dict:
    c_bg = target_delta_i()
    rd_ratio = 1.0 / math.sqrt(1.0 + c_bg)
    required = required_rd_ratio()
    points = [
        {
            "screening": s,
            "c_background": c_bg,
            "c_cmb_effective": s * c_bg,
            "a_center": A_CENTER,
            "width": WIDTH,
        }
        for s in SCREEN_GRID
    ]
    if not execute:
        return {
            "description": "Screened projection scan: full pre-drag background contraction for r_d, reduced CMB-effective G_eff.",
            "status": "screened-rd-cmb-projection-scan-dry",
            "points": points,
            "rd_ratio_background": rd_ratio,
            "required_rd_ratio": required,
            "full_cosmology_prediction_ready_no_fit": False,
        }
    ref = reference_chi2()
    original = SOURCE_PATH.read_text(encoding="utf-8")
    rows = []
    try:
        for point in points:
            SOURCE_PATH.write_text(original, encoding="utf-8")
            set_profile_and_geff(A_CENTER, WIDTH, float(point["c_cmb_effective"]))
            build_code = build_fork()
            result = run_cobaya() if build_code == 0 else {"returncode": build_code, "chi2_CMB": None}
            deltas = {
                f"delta_{key}": result[key] - ref[key]
                for key in ref
                if result.get(key) is not None
            }
            rows.append({**point, "rd_ratio_background": rd_ratio, "rd_ratio_residual": rd_ratio - required, "build_returncode": build_code, **result, **deltas})
    finally:
        SOURCE_PATH.write_text(original, encoding="utf-8")
        build_fork()
    valid = [row for row in rows if row.get("delta_chi2_CMB") is not None]
    planck_ok = [row for row in valid if row["delta_chi2_CMB"] < 0.0]
    best = min(valid, key=lambda row: row["delta_chi2_CMB"]) if valid else None
    best_joint = min(
        valid,
        key=lambda row: abs(row["rd_ratio_residual"]) * 10000.0 + max(row["delta_chi2_CMB"], 0.0),
    ) if valid else None
    return {
        "description": "Screened projection scan: full pre-drag background contraction for r_d, reduced CMB-effective G_eff.",
        "status": "screened-rd-cmb-projection-scan-run",
        "rd_ratio_background": rd_ratio,
        "required_rd_ratio": required,
        "rd_ratio_residual": rd_ratio - required,
        "rows": rows,
        "best_planck": best,
        "best_joint": best_joint,
        "planck_improving_points": planck_ok,
        "screening_window_found": bool(planck_ok and abs(rd_ratio - required) < 0.005),
        "full_cosmology_prediction_ready_no_fit": False,
        "next_required": "Derive the screening factor geometrically; current scan is a projection diagnostic, not a no-fit proof.",
    }


def render_markdown(payload: dict) -> str:
    best = payload.get("best_planck") or {}
    lines = [
        "# P0 EFT Screened r_d/CMB Projection Scan",
        "",
        payload["description"],
        "",
        f"Status: `{payload['status']}`",
        f"r_d background ratio: `{payload['rd_ratio_background']}`",
        f"required r_d ratio: `{payload['required_rd_ratio']}`",
        f"screening window found: `{payload.get('screening_window_found', False)}`",
        f"best Planck screening: `{best.get('screening')}`",
        f"best delta chi2 CMB: `{best.get('delta_chi2_CMB')}`",
        "",
        "| s | c_bg | c_cmb | delta CMB | delta highl | delta lensing |",
        "|---:|---:|---:|---:|---:|---:|",
    ]
    for row in payload.get("rows", []):
        lines.append(
            f"| {row['screening']} | {row['c_background']} | {row['c_cmb_effective']} | "
            f"{row.get('delta_chi2_CMB')} | {row.get('delta_chi2_highl')} | {row.get('delta_chi2_lensing')} |"
        )
    return "\n".join(lines) + "\n"


def write_reports(execute: bool = True) -> dict:
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    payload = build_payload(execute=execute)
    headers = ["screening", "c_background", "c_cmb_effective", "rd_ratio_background", "rd_ratio_residual", "delta_chi2_CMB", "delta_chi2_highl", "delta_chi2_lensing", "chi2_CMB", "returncode"]
    CSV_PATH.write_text(
        "\n".join([",".join(headers)] + [",".join(str(row.get(h, "")) for h in headers) for row in payload.get("rows", [])]) + "\n",
        encoding="utf-8",
    )
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
