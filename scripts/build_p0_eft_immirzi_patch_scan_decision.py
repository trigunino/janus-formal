from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_eft_immirzi_patch_scan_decision.md")
JSON_PATH = Path("outputs/reports/p0_eft_immirzi_patch_scan_decision.json")
SCAN_PATH = Path("outputs/reports/p0_eft_immirzi_patch_mini_scan.json")


def build_payload() -> dict:
    scan = json.loads(SCAN_PATH.read_text(encoding="utf-8"))
    best = scan.get("best") or {}
    return {
        "description": "Decision from the active Immirzi perturbation mini-scan.",
        "status": "immirzi-patch-scan-decision-recorded",
        "scan_grid_size": scan.get("grid_size"),
        "valid_points": scan.get("valid_points"),
        "best": best,
        "best_chi2_CMB": best.get("chi2_CMB"),
        "planck_accepted": bool(scan.get("planck_accepted")),
        "coherent_patch_simple_branch_excluded": not bool(scan.get("planck_accepted")),
        "supersedes_previous_single_gate": True,
        "full_cosmology_prediction_ready_no_fit": False,
        "next_required": (
            "Freeze the simple Immirzi CMB branch as excluded, or derive new reionization/lowE physics "
            "outside the current pre-drag patch."
        ),
    }


def render_markdown(payload: dict) -> str:
    best = payload["best"]
    return "\n".join(
        [
            "# P0 EFT Immirzi Patch Scan Decision",
            "",
            payload["description"],
            "",
            f"Status: {payload['status']}",
            f"Planck accepted: {payload['planck_accepted']}",
            f"Simple branch excluded: {payload['coherent_patch_simple_branch_excluded']}",
            f"Supersedes previous single gate: {payload['supersedes_previous_single_gate']}",
            "",
            "## Best Mini-Scan Point",
            "",
            f"- delta_i: `{best.get('delta_i')}`",
            f"- width: `{best.get('width')}`",
            f"- chi2 CMB: `{best.get('chi2_CMB')}`",
            f"- highl: `{best.get('chi2_highl')}`",
            f"- lowE: `{best.get('chi2_lowl_EE')}`",
            f"- lensing: `{best.get('chi2_lensing')}`",
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
