from __future__ import annotations

from pathlib import Path
import json
import sys

if __package__ in (None, ""):
    sys.path.append(str(Path(__file__).resolve().parents[1]))

from scripts.build_p0_eft_run10b_orbifold_flux_integer_theorem import build_payload as build_run10b
from scripts.build_p0_eft_run10b_spin_connection_gauge_fix import build_payload as build_gauge
from scripts.build_p0_eft_run10b_holonomy_quantum_normalized import (
    build_payload as build_quantum,
)
from scripts.build_p0_eft_run10b_normalized_flux_integer import build_payload as build_integer
from scripts.build_p0_eft_run10b_integer_flux_law import build_payload as build_integer_law


REPORT_PATH = Path("outputs/reports/p0_eft_run10b_flux_quantization_law.md")
JSON_PATH = Path("outputs/reports/p0_eft_run10b_flux_quantization_law.json")


def build_payload() -> dict:
    run10b = build_run10b()
    gauge = build_gauge()
    quantum = build_quantum()
    integer = build_integer()
    integer_law = build_integer_law()
    return {
        "description": "RUN 10B phase 3: normalized holonomy flux quantization law scaffold.",
        "frozen_sectors": run10b["frozen_sectors"],
        "quantization_law": {
            "lean_module": "P0EFTOrbifoldFluxQuantizationLaw",
            "normalization_phase_module": "P0EFTOrbifoldHolonomyQuantumNormalization",
            "spin_connection_gauge_fix_module": gauge["spin_connection_gauge_fix"]["lean_module"],
            "holonomy_quantum_normalized_module": quantum["holonomy_quantum_normalized"]["lean_module"],
            "normalized_flux_integer_module": integer["normalized_flux_integer"]["lean_module"],
            "integer_flux_law_module": integer_law["integer_flux_law"]["lean_module"],
            "cycle_condition": "singular cycle around Sigma is compact",
            "connection_condition": "spin connection restricts to the orbifold cycle",
            "normalization": "flux divided by holonomy quantum",
            "integer_condition": "normalized flux is an integer",
        },
        "logical_arrow": {
            "quantization_law": "fluxQuantizationLawClosed",
            "integer_flux_data": "integerFluxDataClosed",
            "branch_indices": "janusBranchIndicesForced",
        },
        "theorem_status": {
            "run10b_flux_quantization_law_interface_ready": True,
            "quantization_law_to_integer_flux_arrow_formalized": True,
            "run10b_holonomy_quantum_normalization_interface_ready": True,
            "normalization_to_flux_law_arrow_formalized": True,
            "spin_connection_restricts_to_orbifold_cycle_proved": True,
            "holonomy_quantum_normalized_proved": True,
            "normalized_flux_integer_proved": True,
            "integer_flux_law_proved": True,
            "orbifold_global_theorem_proved": False,
            "full_cosmology_prediction_ready_no_fit": False,
        },
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 EFT RUN 10B Flux Quantization Law",
        "",
        payload["description"],
        "",
        "## Quantization Law",
    ]
    lines.extend(f"- {key}: {value}" for key, value in payload["quantization_law"].items())
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
