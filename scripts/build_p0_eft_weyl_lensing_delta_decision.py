from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_eft_weyl_lensing_delta_decision.md")
JSON_PATH = Path("outputs/reports/p0_eft_weyl_lensing_delta_decision.json")
SCAN_PATH = Path("outputs/reports/p0_eft_weyl_lensing_delta_scan.json")


def build_payload() -> dict:
    scan = json.loads(SCAN_PATH.read_text(encoding="utf-8"))
    best_total = scan["best"]
    rows = [row for row in scan["rows"] if row.get("delta_chi2_CMB") is not None]
    balanced = [
        row for row in rows
        if row["delta_chi2_CMB"] < 0.0 and row["delta_chi2_lensing"] < 5.0
    ]
    best_balanced = min(balanced, key=lambda row: row["delta_chi2_CMB"]) if balanced else None
    return {
        "description": "Decision for calibrated Weyl/lensing delta-chi2 scan.",
        "status": "weyl-lensing-delta-decision-recorded",
        "best_total": best_total,
        "best_balanced": best_balanced,
        "total_delta_window_found": best_total["delta_chi2_CMB"] < 0.0,
        "strict_lensing_closed_at_best_total": best_total["delta_chi2_lensing"] < 5.0,
        "balanced_window_found": best_balanced is not None,
        "full_cosmology_prediction_ready_no_fit": False,
        "next_required": (
            "Derive a geometric relation for c_weyl_transfer and c_lensing_source. "
            "The best total point improves CMB but over-amplifies lensing; the balanced window is weaker."
        ),
    }


def render_markdown(payload: dict) -> str:
    total = payload["best_total"]
    balanced = payload["best_balanced"] or {}
    return "\n".join(
        [
            "# P0 EFT Weyl/Lensing Delta Decision",
            "",
            payload["description"],
            "",
            f"Status: {payload['status']}",
            f"Total delta window found: {payload['total_delta_window_found']}",
            f"Strict lensing closed at best total: {payload['strict_lensing_closed_at_best_total']}",
            f"Balanced window found: {payload['balanced_window_found']}",
            f"Full no-fit ready: {payload['full_cosmology_prediction_ready_no_fit']}",
            "",
            "## Best Total",
            "",
            f"- c_weyl_transfer: `{total.get('c_weyl_transfer')}`",
            f"- c_lensing_source: `{total.get('c_lensing_source')}`",
            f"- delta chi2 CMB: `{total.get('delta_chi2_CMB')}`",
            f"- delta lensing: `{total.get('delta_chi2_lensing')}`",
            "",
            "## Best Balanced",
            "",
            f"- c_weyl_transfer: `{balanced.get('c_weyl_transfer')}`",
            f"- c_lensing_source: `{balanced.get('c_lensing_source')}`",
            f"- delta chi2 CMB: `{balanced.get('delta_chi2_CMB')}`",
            f"- delta lensing: `{balanced.get('delta_chi2_lensing')}`",
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


if __name__ == "__main__":
    main()
