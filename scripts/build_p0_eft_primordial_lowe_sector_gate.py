from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_eft_primordial_lowe_sector_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_primordial_lowe_sector_gate.json")
SCAN_PATH = Path("outputs/reports/p0_eft_immirzi_patch_mini_scan.json")
ACCEPTANCE_CHI2 = 15.0


def build_payload() -> dict:
    scan = json.loads(SCAN_PATH.read_text(encoding="utf-8"))
    best = scan.get("best") or {}
    chi2_cmb = float(best.get("chi2_CMB"))
    chi2_highl = float(best.get("chi2_highl"))
    chi2_lowe = float(best.get("chi2_lowl_EE"))
    chi2_lowl_tt = float(best.get("chi2_lowl_TT"))
    chi2_lensing = float(best.get("chi2_lensing"))
    chi2_without_lowe = chi2_cmb - chi2_lowe
    chi2_without_highl = chi2_cmb - chi2_highl
    lowe_only_can_rescue = chi2_without_lowe < ACCEPTANCE_CHI2
    highl_only_can_rescue = chi2_without_highl < ACCEPTANCE_CHI2
    highl_fraction = chi2_highl / chi2_cmb
    lowe_fraction = chi2_lowe / chi2_cmb

    return {
        "description": "Gate deciding whether a new reionization/lowE sector alone can rescue the CMB branch.",
        "status": "primordial-lowe-sector-gate-recorded",
        "source_scan": str(SCAN_PATH),
        "acceptance_chi2": ACCEPTANCE_CHI2,
        "best_active_patch": {
            "delta_i": best.get("delta_i"),
            "width": best.get("width"),
            "chi2_CMB": chi2_cmb,
            "chi2_highl": chi2_highl,
            "chi2_lowl_TT": chi2_lowl_tt,
            "chi2_lowl_EE": chi2_lowe,
            "chi2_lensing": chi2_lensing,
        },
        "chi2_if_lowE_EE_were_perfect": chi2_without_lowe,
        "chi2_if_highl_were_perfect": chi2_without_highl,
        "highl_fraction_of_chi2": highl_fraction,
        "lowE_EE_fraction_of_chi2": lowe_fraction,
        "reionization_lowE_only_excluded": not lowe_only_can_rescue,
        "highl_only_excluded": not highl_only_can_rescue,
        "requires_combined_primordial_highl_and_lowE_sector": (
            not lowe_only_can_rescue and not highl_only_can_rescue and highl_fraction > 0.5
        ),
        "full_cosmology_prediction_ready_no_fit": False,
        "next_required": (
            "Derive a coupled primordial transfer plus lowE/reionization sector; neither lowE-only "
            "nor high-l-only can rescue the tested branch."
        ),
    }


def render_markdown(payload: dict) -> str:
    best = payload["best_active_patch"]
    return "\n".join(
        [
            "# P0 EFT Primordial/lowE Sector Gate",
            "",
            payload["description"],
            "",
            f"Status: {payload['status']}",
            f"Reionization/lowE-only excluded: {payload['reionization_lowE_only_excluded']}",
            f"High-l-only excluded: {payload['highl_only_excluded']}",
            f"Requires combined primordial high-l and lowE sector: {payload['requires_combined_primordial_highl_and_lowE_sector']}",
            f"Full no-fit ready: {payload['full_cosmology_prediction_ready_no_fit']}",
            "",
            "## Best Active Patch",
            "",
            f"- delta_i: `{best['delta_i']}`",
            f"- width: `{best['width']}`",
            f"- chi2 CMB: `{best['chi2_CMB']}`",
            f"- chi2 high-l: `{best['chi2_highl']}`",
            f"- chi2 lowE EE: `{best['chi2_lowl_EE']}`",
            "",
            "## Diagnostic",
            "",
            f"- chi2 if lowE EE were perfect: `{payload['chi2_if_lowE_EE_were_perfect']}`",
            f"- chi2 if high-l were perfect: `{payload['chi2_if_highl_were_perfect']}`",
            f"- high-l fraction of chi2: `{payload['highl_fraction_of_chi2']}`",
            f"- lowE EE fraction of chi2: `{payload['lowE_EE_fraction_of_chi2']}`",
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
