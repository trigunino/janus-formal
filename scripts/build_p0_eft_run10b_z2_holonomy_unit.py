from __future__ import annotations

from pathlib import Path
import json
import sys

if __package__ in (None, ""):
    sys.path.append(str(Path(__file__).resolve().parents[1]))

from scripts.build_p0_eft_run10b_holonomy_quantum_normalization import (
    build_payload as build_norm,
)
from scripts.build_p0_eft_run10b_singular_cycle_generator import (
    build_payload as build_cycle,
)
from scripts.build_p0_eft_run10b_generator_holonomy_unit import (
    build_payload as build_unit,
)


REPORT_PATH = Path("outputs/reports/p0_eft_run10b_z2_holonomy_unit.md")
JSON_PATH = Path("outputs/reports/p0_eft_run10b_z2_holonomy_unit.json")


def build_payload() -> dict:
    norm = build_norm()
    cycle = build_cycle()
    unit = build_unit()
    return {
        "description": "RUN 10B phase 5: Z2 generator holonomy unit scaffold.",
        "frozen_sectors": norm["frozen_sectors"],
        "z2_holonomy_unit": {
            "lean_module": "P0EFTOrbifoldZ2HolonomyUnit",
            "group_law_module": "P0EFTOrbifoldZ2GroupLaw",
            "singular_cycle_phase_module": cycle["singular_cycle_generator"]["lean_module"],
            "generator_holonomy_unit_module": unit["generator_holonomy_unit"]["lean_module"],
            "generator": "Z2 orbifold generator",
            "order": "generator has order two",
            "cycle": "singular cycle represents the Z2 generator",
            "unit": "holonomy unit fixed by the generator",
        },
        "logical_arrow": {
            "z2_unit": "z2HolonomyUnitClosed",
            "normalization": "holonomyQuantumNormalizationClosed",
            "flux_law": "fluxQuantizationLawClosed",
        },
        "theorem_status": {
            "run10b_z2_holonomy_unit_interface_ready": True,
            "z2_unit_to_normalization_arrow_formalized": True,
            "z2_generator_order_two_proved": True,
            "generator_square_transported_to_orbifold": True,
            "singular_cycle_represents_z2_generator_proved": True,
            "around_sigma_maps_to_generator": True,
            "holonomy_unit_chosen_by_orbifold_generator_proved": True,
            "z2_holonomy_unit_closed": True,
            "full_cosmology_prediction_ready_no_fit": False,
        },
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 EFT RUN 10B Z2 Holonomy Unit",
        "",
        payload["description"],
        "",
        "## Z2 Holonomy Unit",
    ]
    lines.extend(f"- {key}: {value}" for key, value in payload["z2_holonomy_unit"].items())
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
