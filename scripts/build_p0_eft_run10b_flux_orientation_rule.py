from __future__ import annotations

from pathlib import Path
import json
import sys

if __package__ in (None, ""):
    sys.path.append(str(Path(__file__).resolve().parents[1]))

from scripts.build_p0_eft_run10b_orbifold_flux_integer_theorem import build_payload as build_run10b
from scripts.build_p0_eft_run10b_janus_orientation_rule import build_payload as build_orientation


REPORT_PATH = Path("outputs/reports/p0_eft_run10b_flux_orientation_rule.md")
JSON_PATH = Path("outputs/reports/p0_eft_run10b_flux_orientation_rule.json")


def build_payload() -> dict:
    run10b = build_run10b()
    orientation = build_orientation()
    return {
        "description": "RUN 10B phase 2: Janus flux orientation rule scaffold.",
        "frozen_sectors": run10b["frozen_sectors"],
        "orientation_rule": {
            "lean_module": "P0EFTOrbifoldFluxOrientationRule",
            "janus_orientation_rule_module": orientation["janus_orientation_rule"]["lean_module"],
            "janus_normal": "fixed",
            "mirror_normal": "fixed",
            "positive_sector": "multiplicity two",
            "negative_sector": "multiplicity one",
        },
        "logical_arrow": {
            "orientation_rule": "orientationRuleClosed",
            "branch_selection": "janusBranchIndicesForced",
            "downstream": "branchIndicesComputed",
        },
        "theorem_status": {
            "run10b_orientation_rule_interface_ready": True,
            "orientation_to_branch_selection_arrow_formalized": True,
            "janus_orientation_rule_proved": True,
            "integer_flux_law_proved": True,
            "orbifold_global_theorem_proved": True,
            "full_cosmology_prediction_ready_no_fit": False,
        },
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 EFT RUN 10B Flux Orientation Rule",
        "",
        payload["description"],
        "",
        "## Orientation Rule",
    ]
    lines.extend(f"- {key}: {value}" for key, value in payload["orientation_rule"].items())
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
