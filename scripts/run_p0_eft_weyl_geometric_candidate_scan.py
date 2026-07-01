from __future__ import annotations

from pathlib import Path
import json
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from scripts.run_p0_eft_weyl_lensing_delta_scan import build_payload


REPORT_PATH = Path("outputs/reports/p0_eft_weyl_geometric_candidate_scan.md")
JSON_PATH = Path("outputs/reports/p0_eft_weyl_geometric_candidate_scan.json")
CSV_PATH = Path("outputs/reports/p0_eft_weyl_geometric_candidate_scan.csv")

CANDIDATES = {
    "one_over_48": 1.0 / 48.0,
    "one_over_40": 1.0 / 40.0,
    "one_over_36": 1.0 / 36.0,
    "empirical_003": 0.03,
    "one_over_32": 1.0 / 32.0,
}


def candidate_points() -> list[dict[str, float | str]]:
    return [
        {"label": label, "c_weyl_transfer": value, "c_lensing_source": 0.0}
        for label, value in CANDIDATES.items()
    ]


def build_candidate_payload(execute: bool = True) -> dict:
    raw_points = candidate_points()
    points = [
        {"c_weyl_transfer": float(point["c_weyl_transfer"]), "c_lensing_source": 0.0}
        for point in raw_points
    ]
    payload = build_payload(points=points, execute=execute)
    for row, point in zip(payload["rows"], raw_points, strict=False):
        row["label"] = point["label"]
    payload["description"] = "Calibrated Planck delta-chi2 scan for rational geometric Weyl candidates."
    payload["status"] = "weyl-geometric-candidate-scan-run" if execute else "weyl-geometric-candidate-scan-dry"
    valid = [row for row in payload["rows"] if row.get("delta_chi2_CMB") is not None]
    payload["best"] = min(valid, key=lambda row: row["delta_chi2_CMB"]) if valid else None
    one_over_36 = next((row for row in valid if row.get("label") == "one_over_36"), None)
    empirical = next((row for row in valid if row.get("label") == "empirical_003"), None)
    payload["one_over_36"] = one_over_36
    payload["empirical_003"] = empirical
    payload["one_over_36_viable"] = bool(one_over_36 and one_over_36["delta_chi2_CMB"] < 0.0 and one_over_36["delta_chi2_lensing"] < 5.0)
    payload["full_cosmology_prediction_ready_no_fit"] = False
    return payload


def render_markdown(payload: dict) -> str:
    best = payload["best"] or {}
    one = payload["one_over_36"] or {}
    return "\n".join(
        [
            "# P0 EFT Weyl Geometric Candidate Scan",
            "",
            payload["description"],
            "",
            f"Status: {payload['status']}",
            f"Best label: `{best.get('label')}`",
            f"1/36 viable: {payload['one_over_36_viable']}",
            f"Full no-fit ready: {payload['full_cosmology_prediction_ready_no_fit']}",
            "",
            "## Best",
            "",
            f"- c_weyl_transfer: `{best.get('c_weyl_transfer')}`",
            f"- delta chi2 CMB: `{best.get('delta_chi2_CMB')}`",
            f"- delta lensing: `{best.get('delta_chi2_lensing')}`",
            "",
            "## Candidate 1/36",
            "",
            f"- c_weyl_transfer: `{one.get('c_weyl_transfer')}`",
            f"- delta chi2 CMB: `{one.get('delta_chi2_CMB')}`",
            f"- delta lensing: `{one.get('delta_chi2_lensing')}`",
            "",
        ]
    )


def write_reports(report_path: Path = REPORT_PATH, json_path: Path = JSON_PATH) -> dict:
    payload = build_candidate_payload()
    headers = [
        "label", "c_weyl_transfer", "delta_chi2_CMB", "delta_chi2_highl",
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
