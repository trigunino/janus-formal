from __future__ import annotations

from pathlib import Path
import json
import sys

if __package__ in (None, ""):
    sys.path.append(str(Path(__file__).resolve().parents[1]))

REPORT_PATH = Path("outputs/reports/p0_eft_run10b_singular_cycle_generator.md")
JSON_PATH = Path("outputs/reports/p0_eft_run10b_singular_cycle_generator.json")


def build_payload() -> dict:
    return {
        "description": "RUN 10B phase 6: singular cycle generator scaffold.",
        "frozen_sectors": {
            "growth_solver": "read-only",
            "sdss_eboss_data": "read-only",
            "holst_membrane_fit": "read-only",
        },
        "singular_cycle_generator": {
            "lean_module": "P0EFTOrbifoldSingularCycleGenerator",
            "cycle": "aroundSigma",
            "quotient_projection": "M5/Z2 -> Z2",
            "map": "aroundSigma -> generator",
            "target": "singularCycleRepresentsZ2Generator",
        },
        "logical_arrow": {
            "concrete_map": "around_sigma_maps_to_z2_generator",
            "transport": "singularCycleRepresentsGeneratorDerived",
            "holonomy_unit": "z2HolonomyUnitClosed",
        },
        "theorem_status": {
            "run10b_singular_cycle_generator_ready": True,
            "singular_cycle_represents_z2_generator_proved": True,
            "around_sigma_maps_to_generator": True,
            "holonomy_unit_chosen_by_orbifold_generator_proved": False,
            "full_cosmology_prediction_ready_no_fit": False,
        },
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 EFT RUN 10B Singular Cycle Generator",
        "",
        payload["description"],
        "",
        "## Singular Cycle Generator",
    ]
    lines.extend(f"- {key}: {value}" for key, value in payload["singular_cycle_generator"].items())
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
