from __future__ import annotations

from pathlib import Path
import json
import sys

if __package__ in (None, ""):
    sys.path.append(str(Path(__file__).resolve().parents[1]))

from scripts.build_p0_eft_run10b_normalized_flux_integer import build_payload as build_integer


REPORT_PATH = Path("outputs/reports/p0_eft_run10b_integer_flux_law.md")
JSON_PATH = Path("outputs/reports/p0_eft_run10b_integer_flux_law.json")


def build_payload() -> dict:
    integer = build_integer()
    return {
        "description": "RUN 10B phase 11: integer flux law scaffold.",
        "frozen_sectors": integer["frozen_sectors"],
        "integer_flux_law": {
            "lean_module": "P0EFTOrbifoldIntegerFluxLaw",
            "normalized_flux_integer_module": integer["normalized_flux_integer"]["lean_module"],
            "cycle": "singular cycle around Sigma",
            "period": "Z2 holonomy period is integer",
            "law": "integerFluxLawDerived",
        },
        "logical_arrow": {
            "integer_flux_law": "integerFluxLawDerived",
            "integer_flux_data": "integerFluxDataClosed",
            "branch_indices": "janusBranchIndicesForced",
        },
        "theorem_status": {
            "run10b_integer_flux_law_ready": True,
            "integer_flux_law_proved": True,
            "z2_holonomy_period_integer": True,
            "janus_orientation_rule_proved": False,
            "orbifold_global_theorem_proved": False,
            "full_cosmology_prediction_ready_no_fit": False,
        },
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 EFT RUN 10B Integer Flux Law",
        "",
        payload["description"],
        "",
        "## Integer Flux Law",
    ]
    lines.extend(f"- {key}: {value}" for key, value in payload["integer_flux_law"].items())
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
