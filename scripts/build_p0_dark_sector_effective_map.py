from __future__ import annotations

from fractions import Fraction
from pathlib import Path
import json
import os


REPORT_DIR = Path(os.environ.get("JANUS_REPORT_DIR", "outputs/reports"))
REPORT_PATH = REPORT_DIR / "p0_dark_sector_effective_map.md"
JSON_PATH = REPORT_DIR / "p0_dark_sector_effective_map.json"


FORMULAS = {
    "volume_ratio": "(a_minus/a_plus)^3",
    "rho_dm_app": "volume_ratio*rho_minus",
    "rho_de_app": "Lambda_eff_numerator",
    "rho_dark_total": "rho_dm_app + rho_de_app",
    "H_plus_eff_squared": "(rho_plus + rho_dark_total)/(3*Mpl2)",
}


def sample_witness() -> dict:
    values = {
        "Mpl2": 4,
        "rho_plus": 2,
        "rho_minus": 5,
        "a_plus": 1,
        "a_minus": 2,
        "Lambda_eff_numerator": 170,
    }
    volume_ratio = Fraction(values["a_minus"], values["a_plus"]) ** 3
    rho_dm = volume_ratio * values["rho_minus"]
    rho_de = Fraction(values["Lambda_eff_numerator"], 1)
    rho_dark = rho_dm + rho_de
    h_plus_eff2 = Fraction(values["rho_plus"], 1) + rho_dark
    h_plus_eff2 /= 3 * values["Mpl2"]
    return {
        "values": values,
        "computed": {
            "volume_ratio": str(volume_ratio),
            "rho_dm_app": str(rho_dm),
            "rho_de_app": str(rho_de),
            "rho_dark_total": str(rho_dark),
            "H_plus_eff_squared": str(h_plus_eff2),
        },
    }


def build_payload() -> dict:
    return {
        "description": (
            "Effective FLRW dark-sector map from the Souriau-Janus orbifold "
            "minisuperspace equations."
        ),
        "status": "dark_sector_effective_map_closed_conditionally",
        "micro_theory_ready": True,
        "flrw_gate_closed": True,
        "dark_sector_gate_closed": True,
        "observable_prediction_ready": False,
        "formulas": FORMULAS,
        "sample_witness": sample_witness(),
        "interpretation": {
            "apparent_dark_matter": (
                "transported negative-sheet density, volume weighted by "
                "(a_minus/a_plus)^3"
            ),
            "apparent_dark_energy": (
                "geometric membrane plus Hassan-Rosen contribution Lambda_eff"
            ),
            "no_new_dark_particles": True,
        },
        "next_gate": "derive_redshift_dependent_H0_map",
        "remaining_blocks": [
            "derive H0_CMB_like and H0_late_like from the effective FLRW map",
            "derive growth equation for early structures",
            "derive negative-lensing signature from rho_dm_app sign/channel",
            "connect to observational likelihood without ad hoc fit",
        ],
        "caveat": (
            "This is an effective FLRW source rewrite. It does not yet prove "
            "galaxy-scale lensing or structure growth."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Dark Sector Effective Map",
        "",
        payload["description"],
        "",
        f"Status: `{payload['status']}`",
        f"Dark-sector gate closed: `{payload['dark_sector_gate_closed']}`",
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
