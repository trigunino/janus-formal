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
    run_cobaya,
    reference_chi2,
)


REPORT_PATH = Path("outputs/reports/p0_eft_predrag_background_only_geff_scan.md")
JSON_PATH = Path("outputs/reports/p0_eft_predrag_background_only_geff_scan.json")
CSV_PATH = Path("outputs/reports/p0_eft_predrag_background_only_geff_scan.csv")
DEFICIT_PATH = Path("outputs/reports/p0_eft_early_deficit_carriers.json")


def target_delta_i() -> float:
    return float(json.loads(DEFICIT_PATH.read_text(encoding="utf-8"))["missing_fractional_E2_on_current_radiation_branch"])


def replace_param(text: str, param_name: str, value: float, count: int = 0) -> str:
    pattern = rf"(real\(dl\), parameter :: {re.escape(param_name)} = )[-+0-9.eE]+_dl"
    return re.sub(pattern, rf"\g<1>{value:.16e}_dl", text, count=count)


def set_profile_and_geff(a_center: float, width: float, c_geff: float) -> None:
    text = SOURCE_PATH.read_text(encoding="utf-8")
    text = replace_param(text, "a_drag", a_center)
    text = replace_param(text, "width", width, count=1)
    text = replace_param(text, "c_geff", c_geff)
    text = replace_param(text, "c_immirzi", 0.0)
    text = replace_param(text, "c_coherent_immirzi", 0.0)
    text = replace_param(text, "c_sound", 0.0)
    text = replace_param(text, "c_opacity", 0.0)
    SOURCE_PATH.write_text(text, encoding="utf-8")


def grid() -> list[dict[str, float | str]]:
    delta = target_delta_i()
    return [
        {"label": "tiny_early", "a_center": 1.0e-4, "width": 5.0e-5, "c_geff": 0.01},
        {"label": "small_early", "a_center": 1.0e-4, "width": 5.0e-5, "c_geff": 0.03},
        {"label": "mid_early", "a_center": 1.0e-4, "width": 5.0e-5, "c_geff": 0.06},
        {"label": "target_early", "a_center": 1.0e-4, "width": 5.0e-5, "c_geff": delta},
        {"label": "target_ultra_early", "a_center": 5.0e-5, "width": 2.0e-5, "c_geff": delta},
        {"label": "target_adiabatic", "a_center": 2.5e-4, "width": 1.5e-4, "c_geff": delta},
    ]


def build_payload(execute: bool = True) -> dict:
    points = grid()
    ref = reference_chi2()
    if not execute:
        return {
            "description": "Pre-drag background-only G_eff scan with perturbative Holst stress disabled.",
            "status": "predrag-background-only-geff-scan-dry",
            "points": points,
            "full_cosmology_prediction_ready_no_fit": False,
        }
    original = SOURCE_PATH.read_text(encoding="utf-8")
    rows = []
    try:
        for point in points:
            SOURCE_PATH.write_text(original, encoding="utf-8")
            set_profile_and_geff(float(point["a_center"]), float(point["width"]), float(point["c_geff"]))
            build_code = build_fork()
            result = run_cobaya() if build_code == 0 else {"returncode": build_code, "chi2_CMB": None}
            deltas = {
                f"delta_{key}": result[key] - ref[key]
                for key in ref
                if result.get(key) is not None
            }
            c_geff = float(point["c_geff"])
            rows.append(
                {
                    **point,
                    "predicted_rd_ratio_if_fully_predrag": 1.0 / math.sqrt(1.0 + c_geff),
                    "build_returncode": build_code,
                    **result,
                    **deltas,
                }
            )
    finally:
        SOURCE_PATH.write_text(original, encoding="utf-8")
        build_fork()
    valid = [row for row in rows if row.get("delta_chi2_CMB") is not None]
    best = min(valid, key=lambda row: row["delta_chi2_CMB"]) if valid else None
    return {
        "description": "Pre-drag background-only G_eff scan with perturbative Holst stress disabled.",
        "status": "predrag-background-only-geff-scan-run",
        "rows": rows,
        "best": best,
        "planck_delta_accepted": bool(best and best["delta_chi2_CMB"] < 0.0),
        "full_cosmology_prediction_ready_no_fit": False,
        "next_required": "If background-only still fails, CMB lock requires a genuine recombination/initial-spectrum derivation rather than late source hooks.",
    }


def render_markdown(payload: dict) -> str:
    best = payload.get("best") or {}
    lines = [
        "# P0 EFT Pre-Drag Background-Only G_eff Scan",
        "",
        payload["description"],
        "",
        f"Status: `{payload['status']}`",
        f"Best: `{best.get('label')}`",
        f"Best delta chi2 CMB: `{best.get('delta_chi2_CMB')}`",
        f"Planck delta accepted: `{payload.get('planck_delta_accepted', False)}`",
        "",
        "| point | c_geff | a_center | width | rd ratio proxy | delta CMB | delta highl | delta lensing |",
        "|---|---:|---:|---:|---:|---:|---:|---:|",
    ]
    for row in payload.get("rows", []):
        lines.append(
            f"| {row['label']} | {row['c_geff']} | {row['a_center']} | {row['width']} | "
            f"{row.get('predicted_rd_ratio_if_fully_predrag')} | {row.get('delta_chi2_CMB')} | "
            f"{row.get('delta_chi2_highl')} | {row.get('delta_chi2_lensing')} |"
        )
    return "\n".join(lines) + "\n"


def write_reports(execute: bool = True) -> dict:
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    payload = build_payload(execute=execute)
    headers = [
        "label", "c_geff", "a_center", "width", "predicted_rd_ratio_if_fully_predrag",
        "delta_chi2_CMB", "delta_chi2_highl", "delta_chi2_lensing", "chi2_CMB", "returncode",
    ]
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
