from __future__ import annotations

from pathlib import Path
import json
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from scripts.run_p0_eft_weyl_lensing_delta_scan import build_payload


REPORT_PATH = Path("outputs/reports/p0_eft_weyl_balanced_fine_scan.md")
JSON_PATH = Path("outputs/reports/p0_eft_weyl_balanced_fine_scan.json")
CSV_PATH = Path("outputs/reports/p0_eft_weyl_balanced_fine_scan.csv")
WEYL_FINE_GRID = [0.015, 0.02, 0.025, 0.03, 0.035, 0.04, 0.045]


def fine_points() -> list[dict[str, float]]:
    return [{"c_weyl_transfer": w, "c_lensing_source": 0.0} for w in WEYL_FINE_GRID]


def build_fine_payload(execute: bool = True) -> dict:
    payload = build_payload(points=fine_points(), execute=execute)
    payload["description"] = "Fine calibrated scan for the geometrically motivated balanced route c_lensing_source = 0."
    payload["status"] = "weyl-balanced-fine-scan-run" if execute else "weyl-balanced-fine-scan-dry"
    valid = [row for row in payload["rows"] if row.get("delta_chi2_CMB") is not None]
    balanced = [row for row in valid if row["delta_chi2_CMB"] < 0.0 and row["delta_chi2_lensing"] < 5.0]
    payload["balanced_points"] = balanced
    payload["best_balanced"] = min(balanced, key=lambda row: row["delta_chi2_CMB"]) if balanced else None
    payload["balanced_delta_window_found"] = bool(payload["best_balanced"])
    payload["full_cosmology_prediction_ready_no_fit"] = False
    return payload


def render_markdown(payload: dict) -> str:
    best = payload.get("best_balanced") or payload.get("best") or {}
    return "\n".join(
        [
            "# P0 EFT Weyl Balanced Fine Scan",
            "",
            payload["description"],
            "",
            f"Status: {payload['status']}",
            f"Balanced delta window found: {payload['balanced_delta_window_found']}",
            f"Full no-fit ready: {payload['full_cosmology_prediction_ready_no_fit']}",
            "",
            "## Best Balanced",
            "",
            f"- c_weyl_transfer: `{best.get('c_weyl_transfer')}`",
            f"- c_lensing_source: `{best.get('c_lensing_source')}`",
            f"- delta chi2 CMB: `{best.get('delta_chi2_CMB')}`",
            f"- delta highl: `{best.get('delta_chi2_highl')}`",
            f"- delta lensing: `{best.get('delta_chi2_lensing')}`",
            "",
        ]
    )


def write_reports(report_path: Path = REPORT_PATH, json_path: Path = JSON_PATH) -> dict:
    payload = build_fine_payload()
    headers = [
        "c_weyl_transfer", "c_lensing_source", "delta_chi2_CMB", "delta_chi2_highl",
        "delta_chi2_lensing", "chi2_CMB", "chi2_highl", "chi2_lensing", "returncode",
    ]
    CSV_PATH.write_text(
        "\n".join([",".join(headers)] + [",".join(str(row.get(h, "")) for h in headers) for row in payload["rows"]]) + "\n",
        encoding="utf-8",
    )
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
