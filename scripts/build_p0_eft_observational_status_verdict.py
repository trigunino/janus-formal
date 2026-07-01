from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_eft_observational_status_verdict.md")
JSON_PATH = Path("outputs/reports/p0_eft_observational_status_verdict.json")
CMB_EXCLUSION_PATH = Path("outputs/reports/p0_eft_cmb_simple_branch_exclusion.json")
COMBINED_TARGET_PATH = Path("outputs/reports/p0_eft_combined_primordial_sector_target.json")
LOWE_SCAN_PATH = Path("outputs/reports/p0_eft_lowe_tau_rescue_scan.json")


def read_json(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def build_payload() -> dict:
    cmb = read_json(CMB_EXCLUSION_PATH)
    combined = read_json(COMBINED_TARGET_PATH)
    lowe = read_json(LOWE_SCAN_PATH)
    cmb_simple_excluded = bool(cmb["cmb_simple_branch_excluded_by_planck"])
    lowe_tau_excluded = not bool(lowe["lowe_tau_can_be_tuned"])

    return {
        "description": "Global status separating formal Janus/orbifold closure from observational cosmology readiness.",
        "status": "observational-status-verdict-recorded",
        "formal_janus_orbifold_scaffold_closed": True,
        "late_time_growth_branch_viable_on_sdss_diagonal": True,
        "cmb_simple_branch_excluded_by_planck": cmb_simple_excluded,
        "lowe_tau_only_excluded": lowe_tau_excluded,
        "requires_new_coupled_primordial_sector": bool(
            combined["required_highl_plus_lowE_suppression_fraction"] >= 0.9
        ),
        "full_observational_cosmology_passes": False,
        "full_cosmology_prediction_ready_no_fit": False,
        "short_verdict": (
            "The Janus/orbifold formal scaffold can be closed internally, but the tested cosmological "
            "branch does not pass the full observation stack because Planck CMB excludes the simple "
            "primordial sector."
        ),
        "next_required": (
            "Either derive a genuinely new coupled primordial high-l/lowE/lensing sector, or record "
            "the current Janus-Holst cosmology branch as observationally excluded by Planck."
        ),
    }


def render_markdown(payload: dict) -> str:
    return "\n".join(
        [
            "# P0 EFT Observational Status Verdict",
            "",
            payload["description"],
            "",
            f"Status: {payload['status']}",
            "",
            "## Verdict",
            "",
            payload["short_verdict"],
            "",
            "## Flags",
            "",
            f"- Formal Janus/orbifold scaffold closed: {payload['formal_janus_orbifold_scaffold_closed']}",
            f"- Late-time SDSS growth branch viable: {payload['late_time_growth_branch_viable_on_sdss_diagonal']}",
            f"- CMB simple branch excluded by Planck: {payload['cmb_simple_branch_excluded_by_planck']}",
            f"- lowE tau-only excluded: {payload['lowe_tau_only_excluded']}",
            f"- Requires new coupled primordial sector: {payload['requires_new_coupled_primordial_sector']}",
            f"- Full observational cosmology passes: {payload['full_observational_cosmology_passes']}",
            f"- Full no-fit ready: {payload['full_cosmology_prediction_ready_no_fit']}",
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
