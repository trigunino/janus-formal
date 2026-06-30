from __future__ import annotations

from pathlib import Path
import json
import sys

if __package__ in (None, ""):
    sys.path.append(str(Path(__file__).resolve().parents[1]))

from scripts.build_p0_eft_run10b_integer_flux_law import build_payload as build_integer_law


REPORT_PATH = Path("outputs/reports/p0_eft_run10b_janus_orientation_rule.md")
JSON_PATH = Path("outputs/reports/p0_eft_run10b_janus_orientation_rule.json")


def build_payload() -> dict:
    integer_law = build_integer_law()
    return {
        "description": "RUN 10B phase 12: Janus orientation rule closure.",
        "frozen_sectors": integer_law["frozen_sectors"],
        "janus_orientation_rule": {
            "lean_module": "P0EFTOrbifoldJanusOrientationRule",
            "integer_flux_law_module": integer_law["integer_flux_law"]["lean_module"],
            "positive_sector": "multiplicity two",
            "negative_sector": "multiplicity one",
            "orientation": "Janus normal and mirror normal fixed",
        },
        "logical_arrow": {
            "orientation": "janusOrientationRuleDerived",
            "flux_orientation": "orientationRuleClosed",
            "branch_selection": "janusBranchIndicesForced",
        },
        "theorem_status": {
            "run10b_janus_orientation_rule_ready": True,
            "janus_orientation_rule_proved": True,
            "positive_flux_sector_multiplicity_two_proved": True,
            "negative_flux_sector_multiplicity_one_proved": True,
            "integer_flux_law_proved": True,
            "orbifold_global_theorem_proved": True,
            "full_cosmology_prediction_ready_no_fit": False,
        },
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 EFT RUN 10B Janus Orientation Rule",
        "",
        payload["description"],
        "",
        "## Janus Orientation Rule",
    ]
    lines.extend(f"- {key}: {value}" for key, value in payload["janus_orientation_rule"].items())
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
