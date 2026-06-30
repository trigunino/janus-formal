from __future__ import annotations

from pathlib import Path
import json
import sys

if __package__ in (None, ""):
    sys.path.append(str(Path(__file__).resolve().parents[1]))

from scripts.build_p0_eft_run10b_singular_cycle_generator import build_payload as build_cycle


REPORT_PATH = Path("outputs/reports/p0_eft_run10b_generator_holonomy_unit.md")
JSON_PATH = Path("outputs/reports/p0_eft_run10b_generator_holonomy_unit.json")


def build_payload() -> dict:
    cycle = build_cycle()
    return {
        "description": "RUN 10B phase 7: generator-selected holonomy unit scaffold.",
        "frozen_sectors": cycle["frozen_sectors"],
        "generator_holonomy_unit": {
            "lean_module": "P0EFTOrbifoldGeneratorHolonomyUnit",
            "cycle_module": cycle["singular_cycle_generator"]["lean_module"],
            "generator": "Z2Element.generator",
            "unit": "HolonomyUnit.z2GeneratorUnit",
            "map": "generator -> z2GeneratorUnit",
        },
        "logical_arrow": {
            "concrete_map": "z2_generator_chooses_holonomy_unit",
            "transport": "holonomyUnitChosenByGeneratorDerived",
            "z2_unit": "z2HolonomyUnitClosed",
        },
        "theorem_status": {
            "run10b_generator_holonomy_unit_ready": True,
            "holonomy_unit_chosen_by_orbifold_generator_proved": True,
            "z2_holonomy_unit_closed": True,
            "holonomy_quantum_normalized_proved": False,
            "normalized_flux_integer_proved": False,
            "full_cosmology_prediction_ready_no_fit": False,
        },
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 EFT RUN 10B Generator Holonomy Unit",
        "",
        payload["description"],
        "",
        "## Generator Holonomy Unit",
    ]
    lines.extend(f"- {key}: {value}" for key, value in payload["generator_holonomy_unit"].items())
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
