from __future__ import annotations

import json
from pathlib import Path


REPORTS = Path("outputs/reports")
BASELINE_PATH = REPORTS / "baseline_expansion_scores.md"
JSON_PATH = REPORTS / "p0_eft_janus_z2_observational_alpha_sector_policy_gate.json"
REPORT_PATH = REPORTS / "p0_eft_janus_z2_observational_alpha_sector_policy_gate.md"


def build_payload(baseline_path: Path = BASELINE_PATH) -> dict:
    baseline_exists = baseline_path.exists()
    baseline_text = baseline_path.read_text(encoding="utf-8") if baseline_exists else ""
    has_sn = "Pantheon+" in baseline_text or "supernova" in baseline_text.lower()
    has_bao = "DESI" in baseline_text or "BAO" in baseline_text

    datasets = {
        "SN_primary": ["Pantheon+", "Union3", "DES-SN5YR"],
        "BAO_primary": ["DESI_DR2_BAO"],
        "Hz_optional": ["cosmic_chronometers"],
    }
    alpha_sector_observable = has_sn or has_bao
    absolute_scale_breaking_possible = has_bao
    no_fit_prediction = False
    recommended_minimal_fit = ["SN_Ia", "BAO"]

    return {
        "status": "janus-z2-observational-alpha-sector-policy-gate",
        "active_core": "Z2_tunnel_Sigma",
        "route": "observational_sector_selection",
        "baseline_scores_exist": baseline_exists,
        "baseline_contains_SN": has_sn,
        "baseline_contains_BAO": has_bao,
        "current_dataset_targets": datasets,
        "alpha_sector_observable": alpha_sector_observable,
        "absolute_scale_breaking_possible": absolute_scale_breaking_possible,
        "recommended_minimal_fit": recommended_minimal_fit,
        "fit_policy": {
            "SN_only_allowed": True,
            "SN_only_interpretation": "shape-only / relative distance; alpha scale remains degenerate with calibration",
            "SN_plus_BAO_required_for_scale": True,
            "Hz_optional_cross_check": True,
            "CMB_later_only": True,
        },
        "no_fit_prediction": no_fit_prediction,
        "alpha_selector_ready": alpha_sector_observable and absolute_scale_breaking_possible,
        "classification": "observational_sector_selection_not_no_fit",
        "bibliography_anchor": [
            "Pantheon+",
            "Union3",
            "DES-SN5YR",
            "DESI_DR2_BAO",
        ],
        "interpretation": (
            "Observations can select or constrain the alpha sector. This is a valid "
            "phenomenological program, but it is not a no-fit derivation of alpha."
        ),
        "gate_passed": True,
    }


def write_reports() -> dict:
    payload = build_payload()
    JSON_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(
        "\n".join(
            [
                "# Janus Z2 Observational Alpha Sector Policy Gate",
                "",
                f"Alpha observable: `{payload['alpha_sector_observable']}`",
                f"Scale breaking possible: `{payload['absolute_scale_breaking_possible']}`",
                f"No-fit prediction: `{payload['no_fit_prediction']}`",
                f"Classification: `{payload['classification']}`",
                "",
                payload["interpretation"],
            ]
        ),
        encoding="utf-8",
    )
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
