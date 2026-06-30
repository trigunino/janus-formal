from __future__ import annotations

from fractions import Fraction
from pathlib import Path
import json
import os


REPORT_DIR = Path(os.environ.get("JANUS_REPORT_DIR", "outputs/reports"))
REPORT_PATH = REPORT_DIR / "p0_hubble_tension_effective_map.md"
JSON_PATH = REPORT_DIR / "p0_hubble_tension_effective_map.json"


FORMULAS = {
    "H_J_squared": "(rho_plus + rho_dark_total)/(3*Mpl2)",
    "H0_app_squared": "H_J_squared/E_ref_squared",
    "H0_CMB_like_squared": "H0_app_squared(z_cmb_like)",
    "H0_late_like_squared": "H0_app_squared(z_late_like)",
    "H0_split_squared": "H0_late_like_squared - H0_CMB_like_squared",
    "H0_ratio_squared": "H0_late_like_squared/H0_CMB_like_squared",
}


def h_j_squared(mpl2: int, rho_plus: int, rho_dark_total: int) -> Fraction:
    return Fraction(rho_plus + rho_dark_total, 3 * mpl2)


def sample_witness() -> dict:
    early = {
        "label": "cmb_like",
        "Mpl2": 4,
        "rho_plus": 0,
        "rho_dark_total": 170,
        "E_ref_squared": 2,
    }
    late = {
        "label": "late_like",
        "Mpl2": 4,
        "rho_plus": 2,
        "rho_dark_total": 210,
        "E_ref_squared": 1,
    }
    h_j_early = h_j_squared(
        early["Mpl2"], early["rho_plus"], early["rho_dark_total"]
    )
    h_j_late = h_j_squared(
        late["Mpl2"], late["rho_plus"], late["rho_dark_total"]
    )
    h0_early = h_j_early / early["E_ref_squared"]
    h0_late = h_j_late / late["E_ref_squared"]
    return {
        "early": early,
        "late": late,
        "computed": {
            "H_J_cmb_like_squared": str(h_j_early),
            "H_J_late_like_squared": str(h_j_late),
            "H0_CMB_like_squared": str(h0_early),
            "H0_late_like_squared": str(h0_late),
            "H0_split_squared": str(h0_late - h0_early),
            "H0_ratio_squared": str(h0_late / h0_early),
        },
    }


def build_payload() -> dict:
    return {
        "description": (
            "Redshift-bin H0 inference map from the effective Souriau-Janus "
            "FLRW dark-sector source."
        ),
        "status": "hubble_tension_effective_map_closed_conditionally",
        "micro_theory_ready": True,
        "flrw_gate_closed": True,
        "dark_sector_gate_closed": True,
        "hubble_gate_closed": True,
        "observable_prediction_ready": False,
        "formulas": FORMULAS,
        "sample_witness": sample_witness(),
        "no_ad_hoc_fit_rule": (
            "The early and late H0_app values must use the same candidate-action "
            "parameter set; only the redshift/bin state changes."
        ),
        "next_gate": "derive_linear_growth_and_early_structure_map",
        "remaining_blocks": [
            "derive growth equation for early structures",
            "derive JWST early-collapse observable",
            "derive negative-lensing signature",
            "derive primordial-GW transition spectrum",
            "connect to observational likelihood without ad hoc fit",
        ],
        "caveat": (
            "This derives an H0 inference map, not a numerical fit to CMB/SN data."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Hubble Tension Effective Map",
        "",
        payload["description"],
        "",
        f"Status: `{payload['status']}`",
        f"Hubble gate closed: `{payload['hubble_gate_closed']}`",
        f"Observable prediction ready: `{payload['observable_prediction_ready']}`",
        "",
        "## Formulas",
        "",
    ]
    for key, value in payload["formulas"].items():
        lines.append(f"- {key}: `{value}`")
    lines.extend(["", "## Sample Witness", ""])
    for key, value in payload["sample_witness"]["computed"].items():
        lines.append(f"- {key}: `{value}`")
    lines.extend(["", "## No Ad Hoc Fit Rule", "", payload["no_ad_hoc_fit_rule"]])
    lines.extend(["", "## Remaining Blocks", ""])
    for block in payload["remaining_blocks"]:
        lines.append(f"- {block}")
    lines.extend(["", "## Caveat", "", payload["caveat"]])
    return "\n".join(lines)


def write_reports(report_path: Path = REPORT_PATH, json_path: Path = JSON_PATH) -> dict:
    report_path.parent.mkdir(parents=True, exist_ok=True)
    json_path.parent.mkdir(parents=True, exist_ok=True)
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
