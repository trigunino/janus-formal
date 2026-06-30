from __future__ import annotations

from pathlib import Path
import json
import sys

if __package__ in (None, ""):
    sys.path.append(str(Path(__file__).resolve().parents[1]))

from scripts.build_p0_eft_run8_orbifold_volume_derivation_audit import build_payload as build_run8


REPORT_PATH = Path("outputs/reports/p0_eft_run8_orbifold_euler_characteristic_audit.md")
JSON_PATH = Path("outputs/reports/p0_eft_run8_orbifold_euler_characteristic_audit.json")


def build_payload() -> dict:
    run8 = build_run8()
    return {
        "description": "RUN 8 phase 2: Euler/cover multiplicity scaffold for Vol_+:Vol_-=2:1.",
        "frozen_sectors": run8["frozen_sectors"],
        "euler_cover_interface": {
            "lean_module": "P0EFTOrbifoldEulerCharacteristic",
            "gauge_complex": "asymmetric Janus gauge complex",
            "surface_metric": "induced metric on Sigma",
            "cover_projection": "Z2 branched cover projection",
            "branch_locus": "Janus membrane fixed set",
            "target_multiplicity": "positive sheet 2, negative sheet 1",
        },
        "logical_arrow": {
            "cover_multiplicity": "coverMultiplicityTwoToOne",
            "volume_ratio_input": "asymmetricSheetMultiplicityTwoToOne",
            "volume_derivation": "orbifoldVolumeRatioTwoToOneDerived",
            "local_consequence": "3*a_sigma - 2 = 0",
        },
        "theorem_status": {
            "run8_euler_cover_interface_ready": True,
            "multiplicity_to_ratio_arrow_formalized": True,
            "branch_locus_multiplicity_computed": False,
            "positive_sheet_multiplicity_two_proved": False,
            "negative_sheet_multiplicity_one_proved": False,
            "orbifold_cover_global_theorem_proved": False,
            "full_cosmology_prediction_ready_no_fit": False,
        },
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 EFT RUN 8 Orbifold Euler Characteristic Audit",
        "",
        payload["description"],
        "",
        "## Euler Cover Interface",
    ]
    lines.extend(f"- {key}: {value}" for key, value in payload["euler_cover_interface"].items())
    lines.extend(["", "## Logical Arrow"])
    lines.extend(f"- {key}: {value}" for key, value in payload["logical_arrow"].items())
    lines.extend(["", "## Status"])
    lines.extend(f"- {key}: {value}" for key, value in payload["theorem_status"].items())
    lines.append("")
    return "\n".join(lines)


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
