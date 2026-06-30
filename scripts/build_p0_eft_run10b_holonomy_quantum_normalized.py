from __future__ import annotations

from pathlib import Path
import json
import sys

if __package__ in (None, ""):
    sys.path.append(str(Path(__file__).resolve().parents[1]))

from scripts.build_p0_eft_run10b_generator_holonomy_unit import build_payload as build_unit
from scripts.build_p0_eft_run10b_spin_connection_gauge_fix import build_payload as build_gauge


REPORT_PATH = Path("outputs/reports/p0_eft_run10b_holonomy_quantum_normalized.md")
JSON_PATH = Path("outputs/reports/p0_eft_run10b_holonomy_quantum_normalized.json")


def build_payload() -> dict:
    unit = build_unit()
    gauge = build_gauge()
    return {
        "description": "RUN 10B phase 9: holonomy quantum normalized scaffold.",
        "frozen_sectors": gauge["frozen_sectors"],
        "holonomy_quantum_normalized": {
            "lean_module": "P0EFTOrbifoldHolonomyQuantumNormalized",
            "unit_module": unit["generator_holonomy_unit"]["lean_module"],
            "gauge_module": gauge["spin_connection_gauge_fix"]["lean_module"],
            "normalization": "flux divided by the Z2 generator holonomy unit",
        },
        "logical_arrow": {
            "normalization": "holonomyQuantumNormalizedDerived",
            "flux_law": "fluxQuantizationLawClosed",
        },
        "theorem_status": {
            "run10b_holonomy_quantum_normalized_ready": True,
            "holonomy_quantum_normalized_proved": True,
            "flux_divided_by_holonomy_unit_well_defined": True,
            "normalized_flux_integer_proved": False,
            "integer_flux_law_proved": False,
            "full_cosmology_prediction_ready_no_fit": False,
        },
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 EFT RUN 10B Holonomy Quantum Normalized",
        "",
        payload["description"],
        "",
        "## Holonomy Quantum Normalized",
    ]
    lines.extend(f"- {key}: {value}" for key, value in payload["holonomy_quantum_normalized"].items())
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
