from __future__ import annotations

from pathlib import Path
import json
import sys

if __package__ in (None, ""):
    sys.path.append(str(Path(__file__).resolve().parents[1]))

from scripts.build_p0_eft_run10b_z2_holonomy_unit import build_payload as build_z2_unit


REPORT_PATH = Path("outputs/reports/p0_eft_run10b_z2_group_law.md")
JSON_PATH = Path("outputs/reports/p0_eft_run10b_z2_group_law.json")


def build_payload() -> dict:
    z2_unit = build_z2_unit()
    return {
        "description": "RUN 10B algebraic closure of the Z2 generator order-two law.",
        "frozen_sectors": z2_unit["frozen_sectors"],
        "z2_group_law": {
            "lean_module": "P0EFTOrbifoldZ2GroupLaw",
            "carrier": "{unit, generator}",
            "multiplication": "generator * generator = unit",
            "transport_target": "z2GeneratorOrderTwo",
        },
        "logical_arrow": {
            "concrete_group_law": "generator_square_is_unit",
            "transport": "z2GeneratorOrderTwoDerived",
            "holonomy_unit": "z2HolonomyUnitClosed",
        },
        "theorem_status": {
            "run10b_z2_group_law_ready": True,
            "z2_generator_order_two_proved": True,
            "generator_square_transported_to_orbifold": True,
            "singular_cycle_represents_z2_generator_proved": False,
            "holonomy_unit_chosen_by_orbifold_generator_proved": False,
            "full_cosmology_prediction_ready_no_fit": False,
        },
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 EFT RUN 10B Z2 Group Law",
        "",
        payload["description"],
        "",
        "## Z2 Group Law",
    ]
    lines.extend(f"- {key}: {value}" for key, value in payload["z2_group_law"].items())
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
