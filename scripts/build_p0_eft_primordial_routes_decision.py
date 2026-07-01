from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_eft_primordial_routes_decision.md")
JSON_PATH = Path("outputs/reports/p0_eft_primordial_routes_decision.json")
TWO_MODE_PATH = Path("outputs/reports/p0_eft_two_mode_primordial_scan.json")
VISIBILITY_PATH = Path("outputs/reports/p0_eft_nonlocal_visibility_scan.json")


def read_json(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def build_payload() -> dict:
    two_mode = read_json(TWO_MODE_PATH)
    visibility = read_json(VISIBILITY_PATH)
    two_best = two_mode["best"]
    vis_best = visibility["best"]
    visibility_improves_total = vis_best["chi2_CMB"] < two_best["chi2_CMB"]
    visibility_fixes_lowe = vis_best["chi2_lowl_EE"] < 50.0
    highl_still_bad = vis_best["chi2_highl"] > 2000.0
    routes_excluded_as_sufficient = (
        not two_mode["planck_accepted"]
        and not visibility["planck_accepted"]
        and not visibility_fixes_lowe
        and highl_still_bad
    )

    return {
        "description": "Decision comparing the two-mode and nonlocal visibility primordial CMB routes.",
        "status": "primordial-routes-decision-recorded",
        "two_mode_best": two_best,
        "nonlocal_visibility_best": vis_best,
        "two_mode_planck_accepted": bool(two_mode["planck_accepted"]),
        "nonlocal_visibility_planck_accepted": bool(visibility["planck_accepted"]),
        "nonlocal_visibility_improves_total_chi2": visibility_improves_total,
        "nonlocal_visibility_fixes_lowE": visibility_fixes_lowe,
        "highl_still_bad_after_visibility": highl_still_bad,
        "tested_routes_excluded_as_sufficient": routes_excluded_as_sufficient,
        "full_cosmology_prediction_ready_no_fit": False,
        "next_required": (
            "The nonlocal visibility envelope helps high-l modestly but does not solve lowE. "
            "Next route must alter the polarization source shape itself, not only opacity amplitude."
        ),
    }


def render_markdown(payload: dict) -> str:
    two = payload["two_mode_best"]
    vis = payload["nonlocal_visibility_best"]
    return "\n".join(
        [
            "# P0 EFT Primordial Routes Decision",
            "",
            payload["description"],
            "",
            f"Status: {payload['status']}",
            f"Tested routes sufficient: {not payload['tested_routes_excluded_as_sufficient']}",
            f"Full no-fit ready: {payload['full_cosmology_prediction_ready_no_fit']}",
            "",
            "## Two-Mode Best",
            "",
            f"- theta_pre: `{two.get('theta_pre')}`",
            f"- theta_visibility: `{two.get('theta_visibility')}`",
            f"- chi2 CMB: `{two.get('chi2_CMB')}`",
            f"- lowE: `{two.get('chi2_lowl_EE')}`",
            "",
            "## Nonlocal Visibility Best",
            "",
            f"- c_visibility_memory: `{vis.get('c_visibility_memory')}`",
            f"- chi2 CMB: `{vis.get('chi2_CMB')}`",
            f"- highl: `{vis.get('chi2_highl')}`",
            f"- lowE: `{vis.get('chi2_lowl_EE')}`",
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
