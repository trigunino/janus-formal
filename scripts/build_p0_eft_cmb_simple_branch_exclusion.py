from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_eft_cmb_simple_branch_exclusion.md")
JSON_PATH = Path("outputs/reports/p0_eft_cmb_simple_branch_exclusion.json")
BRANCH_DECISION_PATH = Path("outputs/reports/p0_eft_cmb_branch_decision.json")
PATCH_SCAN_DECISION_PATH = Path("outputs/reports/p0_eft_immirzi_patch_scan_decision.json")


def read_json(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def build_payload() -> dict:
    branch = read_json(BRANCH_DECISION_PATH)
    patch = read_json(PATCH_SCAN_DECISION_PATH)

    route_a_excluded = bool(branch.get("route_a_free_neff_excluded"))
    route_b_excluded = bool(branch.get("route_b_background_only_excluded"))
    coherent_patch_excluded = bool(patch.get("coherent_patch_simple_branch_excluded"))
    simple_branch_excluded = route_a_excluded and route_b_excluded and coherent_patch_excluded

    return {
        "description": "Final exclusion record for the simple Janus-Holst CMB branch tested against Planck.",
        "status": "cmb-simple-branch-exclusion-recorded",
        "route_a_free_neff_excluded": route_a_excluded,
        "route_b_background_only_geff_excluded": route_b_excluded,
        "coherent_immirzi_patch_simple_branch_excluded": coherent_patch_excluded,
        "cmb_simple_branch_excluded_by_planck": simple_branch_excluded,
        "best_active_patch_chi2_CMB": patch.get("best_chi2_CMB"),
        "full_cosmology_prediction_ready_no_fit": False,
        "next_required": (
            "Do not tune this branch further. A viable CMB path now requires new derived physics "
            "outside the tested simple carriers, e.g. a reionization/lowE sector or a different "
            "primordial Immirzi dynamics."
        ),
    }


def render_markdown(payload: dict) -> str:
    return "\n".join(
        [
            "# P0 EFT CMB Simple Branch Exclusion",
            "",
            payload["description"],
            "",
            f"Status: {payload['status']}",
            f"Simple CMB branch excluded by Planck: {payload['cmb_simple_branch_excluded_by_planck']}",
            f"Full no-fit ready: {payload['full_cosmology_prediction_ready_no_fit']}",
            "",
            "## Excluded Routes",
            "",
            f"- Free N_eff carrier: {payload['route_a_free_neff_excluded']}",
            f"- Background-only G_eff carrier: {payload['route_b_background_only_geff_excluded']}",
            f"- Coherent simple Immirzi perturbation patch: {payload['coherent_immirzi_patch_simple_branch_excluded']}",
            "",
            "## Evidence",
            "",
            f"- Best active-patch chi2 CMB: {payload['best_active_patch_chi2_CMB']}",
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
