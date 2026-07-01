from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_eft_combined_primordial_sector_target.md")
JSON_PATH = Path("outputs/reports/p0_eft_combined_primordial_sector_target.json")
LOWE_GATE_PATH = Path("outputs/reports/p0_eft_primordial_lowe_sector_gate.json")
TARGET_CHI2 = 15.0


def build_payload() -> dict:
    gate = json.loads(LOWE_GATE_PATH.read_text(encoding="utf-8"))
    best = gate["best_active_patch"]
    chi2_highl = float(best["chi2_highl"])
    chi2_lowe = float(best["chi2_lowl_EE"])
    chi2_lowl_tt = float(best["chi2_lowl_TT"])
    chi2_lensing = float(best["chi2_lensing"])
    non_highl_lowE_floor = chi2_lowl_tt + chi2_lensing
    remaining_budget = max(TARGET_CHI2 - non_highl_lowE_floor, 0.0)
    current_highl_lowe = chi2_highl + chi2_lowe
    required_residual_fraction = remaining_budget / current_highl_lowe if current_highl_lowe else 0.0
    required_suppression_fraction = 1.0 - required_residual_fraction

    return {
        "description": "Algebraic target for any coupled primordial high-l plus lowE sector.",
        "status": "combined-primordial-sector-target-recorded",
        "target_chi2": TARGET_CHI2,
        "current": {
            "chi2_highl": chi2_highl,
            "chi2_lowl_EE": chi2_lowe,
            "chi2_lowl_TT": chi2_lowl_tt,
            "chi2_lensing": chi2_lensing,
        },
        "non_highl_lowE_floor": non_highl_lowE_floor,
        "remaining_budget_for_highl_plus_lowE": remaining_budget,
        "current_highl_plus_lowE_chi2": current_highl_lowe,
        "required_highl_plus_lowE_residual_fraction": required_residual_fraction,
        "required_highl_plus_lowE_suppression_fraction": required_suppression_fraction,
        "strict_target_possible_without_lowlTT_lensing_work": remaining_budget > 0.0,
        "derived_sector_required": (
            "A viable branch must jointly change the pre-recombination transfer functions and the "
            "reionization/lowE source. The required correction is not a small perturbative tweak."
        ),
        "full_cosmology_prediction_ready_no_fit": False,
    }


def render_markdown(payload: dict) -> str:
    return "\n".join(
        [
            "# P0 EFT Combined Primordial Sector Target",
            "",
            payload["description"],
            "",
            f"Status: {payload['status']}",
            f"Target chi2: `{payload['target_chi2']}`",
            f"Full no-fit ready: {payload['full_cosmology_prediction_ready_no_fit']}",
            "",
            "## Required Correction",
            "",
            f"- non high-l/lowE floor: `{payload['non_highl_lowE_floor']}`",
            f"- remaining budget for high-l + lowE: `{payload['remaining_budget_for_highl_plus_lowE']}`",
            f"- current high-l + lowE chi2: `{payload['current_highl_plus_lowE_chi2']}`",
            f"- required residual fraction: `{payload['required_highl_plus_lowE_residual_fraction']}`",
            f"- required suppression fraction: `{payload['required_highl_plus_lowE_suppression_fraction']}`",
            "",
            "## Interpretation",
            "",
            payload["derived_sector_required"],
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
