from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_eft_primordial_theta_scan_decision.md")
JSON_PATH = Path("outputs/reports/p0_eft_primordial_theta_scan_decision.json")
SCAN_PATH = Path("outputs/reports/p0_eft_primordial_theta_scan.json")


def build_payload() -> dict:
    scan = json.loads(SCAN_PATH.read_text(encoding="utf-8"))
    best = scan.get("best") or {}
    rows = [row for row in scan.get("rows", []) if row.get("chi2_CMB") is not None]
    nonzero_rows = [row for row in rows if abs(float(row.get("theta", 0.0))) > 0.0]
    best_nonzero = min(nonzero_rows, key=lambda row: row["chi2_CMB"]) if nonzero_rows else None
    neutral_is_best = best.get("theta") == 0.0
    nonzero_improves = bool(best_nonzero and best_nonzero["chi2_CMB"] < best["chi2_CMB"])
    branch_excluded = neutral_is_best and not nonzero_improves and not bool(scan.get("planck_accepted"))

    return {
        "description": "Decision from the Ward-constrained one-parameter primordial theta scan.",
        "status": "primordial-theta-scan-decision-recorded",
        "best": best,
        "best_nonzero": best_nonzero,
        "neutral_theta_is_best": neutral_is_best,
        "nonzero_theta_improves_planck": nonzero_improves,
        "ward_single_mode_branch_excluded": branch_excluded,
        "full_cosmology_prediction_ready_no_fit": False,
        "next_required": (
            "The one-mode Ward branch is excluded. A viable CMB sector must add a second derived "
            "primordial degree of freedom or a nonlocal visibility source, not just quantize theta."
        ),
    }


def render_markdown(payload: dict) -> str:
    best = payload["best"] or {}
    best_nonzero = payload["best_nonzero"] or {}
    return "\n".join(
        [
            "# P0 EFT Primordial Theta Scan Decision",
            "",
            payload["description"],
            "",
            f"Status: {payload['status']}",
            f"Ward single-mode branch excluded: {payload['ward_single_mode_branch_excluded']}",
            f"Full no-fit ready: {payload['full_cosmology_prediction_ready_no_fit']}",
            "",
            "## Best",
            "",
            f"- theta: `{best.get('theta')}`",
            f"- chi2 CMB: `{best.get('chi2_CMB')}`",
            "",
            "## Best Nonzero",
            "",
            f"- theta: `{best_nonzero.get('theta')}`",
            f"- chi2 CMB: `{best_nonzero.get('chi2_CMB')}`",
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
