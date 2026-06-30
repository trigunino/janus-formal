from __future__ import annotations

from pathlib import Path
import json
import sys

if __package__ in (None, ""):
    sys.path.append(str(Path(__file__).resolve().parents[1]))

from scripts.build_p0_eft_run8_orbifold_euler_characteristic_audit import build_payload as build_euler


REPORT_PATH = Path("outputs/reports/p0_eft_run8_holonomy_flux_quantization_audit.md")
JSON_PATH = Path("outputs/reports/p0_eft_run8_holonomy_flux_quantization_audit.json")


def build_payload() -> dict:
    euler = build_euler()
    return {
        "description": "RUN 8 phase 3: spin-connection holonomy flux quantization scaffold.",
        "frozen_sectors": {
            "run7_aps_pin_spectral_axis": "untouched",
            "numeric_solver": "untouched",
            "sdss_eboss_tables": "untouched",
        },
        "holonomy_flux_interface": {
            "lean_module": "P0EFTOrbifoldHolonomyFluxQuantization",
            "cycle": "singular cycle around Sigma",
            "flux_integral": "integral of spin connection omega^{ab}",
            "quantization_condition": "integer holonomy flux on branched orbifold cycle",
            "target_indices": "positive branch index 2, negative branch index 1",
        },
        "logical_arrow": {
            "flux_quantization": "branchIndicesComputed",
            "euler_multiplicity": "eulerCoverDataClosed",
            "volume_ratio": "orbifoldVolumeRatioTwoToOneDerived",
            "previous_phase": euler["logical_arrow"]["cover_multiplicity"],
        },
        "theorem_status": {
            "run8_holonomy_flux_interface_ready": True,
            "flux_to_branch_index_arrow_formalized": True,
            "flux_quantization_condition_proved": False,
            "positive_branch_index_two_proved": False,
            "negative_branch_index_one_proved": False,
            "orbifold_cover_global_theorem_proved": False,
            "full_cosmology_prediction_ready_no_fit": False,
        },
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 EFT RUN 8 Holonomy Flux Quantization Audit",
        "",
        payload["description"],
        "",
        "## Holonomy Flux Interface",
    ]
    lines.extend(f"- {key}: {value}" for key, value in payload["holonomy_flux_interface"].items())
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
