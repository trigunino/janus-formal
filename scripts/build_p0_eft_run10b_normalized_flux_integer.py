from __future__ import annotations

from pathlib import Path
import json
import sys

if __package__ in (None, ""):
    sys.path.append(str(Path(__file__).resolve().parents[1]))

from scripts.build_p0_eft_run10b_holonomy_quantum_normalized import build_payload as build_quantum


REPORT_PATH = Path("outputs/reports/p0_eft_run10b_normalized_flux_integer.md")
JSON_PATH = Path("outputs/reports/p0_eft_run10b_normalized_flux_integer.json")


def build_payload() -> dict:
    quantum = build_quantum()
    return {
        "description": "RUN 10B phase 10: normalized flux integer scaffold.",
        "frozen_sectors": quantum["frozen_sectors"],
        "normalized_flux_integer": {
            "lean_module": "P0EFTOrbifoldNormalizedFluxInteger",
            "holonomy_quantum_module": quantum["holonomy_quantum_normalized"]["lean_module"],
            "flux": "spin-connection flux divided by the Z2 holonomy quantum",
            "lattice": "normalized flux lands in the integer lattice",
        },
        "logical_arrow": {
            "integer_local": "normalizedFluxIntegerDerived",
            "flux_law": "fluxQuantizationLawClosed",
        },
        "theorem_status": {
            "run10b_normalized_flux_integer_ready": True,
            "normalized_flux_integer_proved": True,
            "normalized_flux_lands_in_integer_lattice": True,
            "integer_flux_law_proved": False,
            "orbifold_global_theorem_proved": False,
            "full_cosmology_prediction_ready_no_fit": False,
        },
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 EFT RUN 10B Normalized Flux Integer",
        "",
        payload["description"],
        "",
        "## Normalized Flux Integer",
    ]
    lines.extend(f"- {key}: {value}" for key, value in payload["normalized_flux_integer"].items())
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
