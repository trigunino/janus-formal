from __future__ import annotations

from pathlib import Path
import json
import sys

if __package__ in (None, ""):
    sys.path.append(str(Path(__file__).resolve().parents[1]))

from scripts.build_p0_eft_run6_global_topology_scaffold import build_payload as build_run6
from scripts.build_p0_eft_run10b_janus_orientation_rule import build_payload as build_orientation


REPORT_PATH = Path("outputs/reports/p0_eft_run8_orbifold_volume_derivation_audit.md")
JSON_PATH = Path("outputs/reports/p0_eft_run8_orbifold_volume_derivation_audit.json")


def build_payload() -> dict:
    run6 = build_run6()
    orientation = build_orientation()
    return {
        "description": "RUN 8 orbifold volume derivation scaffold for Vol_+:Vol_-=2:1.",
        "frozen_sectors": {
            "run7_aps_pin_spectral_axis": "untouched",
            "numeric_solver": "untouched",
            "sdss_eboss_tables": "untouched",
        },
        "orbifold_derivation_interface": {
            "lean_module": "P0EFTOrbifoldVolumeDerivation",
            "euler_phase2_module": "P0EFTOrbifoldEulerCharacteristic",
            "holonomy_phase3_module": "P0EFTOrbifoldHolonomyFluxQuantization",
            "run10b_janus_orientation_rule_module": orientation["janus_orientation_rule"]["lean_module"],
            "quotient": "M5 / Z2",
            "fixed_set": "Janus membrane Sigma",
            "flux_condition": "spin-connection holonomy flux quantized",
            "surface_invariant": "Euler/holonomy class of asymmetric orbifold",
            "target_ratio": "Vol_+:Vol_-=2:1",
        },
        "logical_arrow": {
            "global_topology": "orbifoldVolumeRatioTwoToOneDerived",
            "cover_classification": "globalCoverRatioDerived",
            "local_consequence": "3*a_sigma - 2 = 0",
            "local_residual": run6["local_closed"]["orbifold_3a_sigma_minus_2_residual"],
        },
        "theorem_status": {
            "run8_orbifold_volume_interface_ready": True,
            "run8_euler_cover_interface_ready": True,
            "multiplicity_to_ratio_arrow_formalized": True,
            "run8_holonomy_flux_interface_ready": True,
            "flux_to_branch_index_arrow_formalized": True,
            "flux_quantization_proved": True,
            "euler_surface_class_computed": True,
            "sheet_multiplicity_two_to_one_proved": True,
            "orbifold_cover_global_theorem_proved": True,
            "full_cosmology_prediction_ready_no_fit": False,
        },
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 EFT RUN 8 Orbifold Volume Derivation Audit",
        "",
        payload["description"],
        "",
        "## Frozen Sectors",
    ]
    lines.extend(f"- {key}: {value}" for key, value in payload["frozen_sectors"].items())
    lines.extend(["", "## Orbifold Derivation Interface"])
    lines.extend(f"- {key}: {value}" for key, value in payload["orbifold_derivation_interface"].items())
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
