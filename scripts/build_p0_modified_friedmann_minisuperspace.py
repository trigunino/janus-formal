from __future__ import annotations

from fractions import Fraction
from pathlib import Path
import json
import os


REPORT_DIR = Path(os.environ.get("JANUS_REPORT_DIR", "outputs/reports"))
REPORT_PATH = REPORT_DIR / "p0_modified_friedmann_minisuperspace.md"
JSON_PATH = REPORT_DIR / "p0_modified_friedmann_minisuperspace.json"


def hr_polynomials() -> dict:
    return {
        "x0": "v*N_minus/N_plus",
        "r": "a_minus/a_plus",
        "e0": "1",
        "e1": "x0 + 3*r",
        "e2": "3*x0*r + 3*r^2",
        "e3": "3*x0*r^2 + r^3",
        "U_HR": "e0 + 3*e1 + 3*e2 + e3",
        "U_HR_expanded": (
            "1 + 3*x0 + 9*r + 9*x0*r + 9*r^2 + 3*x0*r^2 + r^3"
        ),
    }


def friedmann_formulas() -> dict:
    return {
        "Lambda_eff_numerator": "T_memb + mHR2*Mpl2*U_HR",
        "H_plus_squared": "(rho_plus + Lambda_eff_numerator)/(3*Mpl2)",
        "H_minus_squared": "(rho_minus + Lambda_eff_numerator)/(3*Mpl2*v^2)",
        "scope": "flat FLRW minisuperspace of the accepted candidate action",
    }


def sample_witness() -> dict:
    values = {
        "Mpl2": 4,
        "mHR2": 1,
        "T_memb": 30,
        "v": 1,
        "N_plus": 1,
        "N_minus": 1,
        "a_plus": 1,
        "a_minus": 1,
        "rho_plus": 0,
        "rho_minus": 0,
    }
    x0 = Fraction(1, 1)
    r = Fraction(1, 1)
    e1 = x0 + 3 * r
    e2 = 3 * x0 * r + 3 * r**2
    e3 = 3 * x0 * r**2 + r**3
    u_hr = 1 + 3 * e1 + 3 * e2 + e3
    lambda_eff = values["T_memb"] + values["mHR2"] * values["Mpl2"] * u_hr
    h_plus2 = Fraction(lambda_eff, 3 * values["Mpl2"])
    h_minus2 = Fraction(lambda_eff, 3 * values["Mpl2"] * values["v"] ** 2)
    return {
        "values": values,
        "computed": {
            "x0": str(x0),
            "r": str(r),
            "U_HR": str(u_hr),
            "Lambda_eff_numerator": str(lambda_eff),
            "H_plus_squared": str(h_plus2),
            "H_minus_squared": str(h_minus2),
        },
    }


def build_payload() -> dict:
    return {
        "description": (
            "Conditional modified Friedmann minisuperspace map for the "
            "Souriau-Janus orbifold candidate action."
        ),
        "status": "flrw_minisuperspace_closed_conditionally",
        "observable_prediction_ready": False,
        "micro_theory_ready": True,
        "flrw_gate_closed": True,
        "hr_polynomials": hr_polynomials(),
        "friedmann_formulas": friedmann_formulas(),
        "sample_witness": sample_witness(),
        "next_gate": "derive_effective_dark_sector_map_from_flrw_sources",
        "remaining_blocks": [
            "interpret Lambda_eff as late-time dark-energy observable",
            "derive apparent dark-matter kernel from negative-sheet sources",
            "derive redshift-dependent H0 split",
            "derive growth equation for early structures",
            "quantify lensing/GW signatures",
            "connect to data likelihoods without ad hoc fit",
        ],
        "caveat": (
            "This closes the flat FLRW minisuperspace algebra of the accepted "
            "candidate action; it is not yet a calibrated cosmological likelihood."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Modified Friedmann Minisuperspace",
        "",
        payload["description"],
        "",
        f"Status: `{payload['status']}`",
        f"FLRW gate closed: `{payload['flrw_gate_closed']}`",
        f"Observable prediction ready: `{payload['observable_prediction_ready']}`",
        "",
        "## Hassan-Rosen FLRW Polynomials",
        "",
    ]
    for key, value in payload["hr_polynomials"].items():
        lines.append(f"- {key}: `{value}`")
    lines.extend(["", "## Friedmann Formulas", ""])
    for key, value in payload["friedmann_formulas"].items():
        lines.append(f"- {key}: `{value}`")
    lines.extend(["", "## Sample Witness", ""])
    for key, value in payload["sample_witness"]["computed"].items():
        lines.append(f"- {key}: `{value}`")
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
