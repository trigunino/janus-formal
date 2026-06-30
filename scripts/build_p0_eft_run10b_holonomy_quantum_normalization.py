from __future__ import annotations

from pathlib import Path
import json
import sys

if __package__ in (None, ""):
    sys.path.append(str(Path(__file__).resolve().parents[1]))

from scripts.build_p0_eft_run10b_flux_quantization_law import build_payload as build_flux_law
from scripts.build_p0_eft_run10b_generator_holonomy_unit import build_payload as build_unit
from scripts.build_p0_eft_run10b_spin_connection_gauge_fix import build_payload as build_gauge
from scripts.build_p0_eft_run10b_holonomy_quantum_normalized import (
    build_payload as build_quantum,
)


REPORT_PATH = Path("outputs/reports/p0_eft_run10b_holonomy_quantum_normalization.md")
JSON_PATH = Path("outputs/reports/p0_eft_run10b_holonomy_quantum_normalization.json")


def build_payload() -> dict:
    flux_law = build_flux_law()
    unit = build_unit()
    gauge = build_gauge()
    quantum = build_quantum()
    return {
        "description": "RUN 10B phase 4: holonomy quantum normalization scaffold.",
        "frozen_sectors": flux_law["frozen_sectors"],
        "holonomy_normalization": {
            "lean_module": "P0EFTOrbifoldHolonomyQuantumNormalization",
            "z2_unit_phase_module": "P0EFTOrbifoldZ2HolonomyUnit",
            "generator_holonomy_unit_module": unit["generator_holonomy_unit"]["lean_module"],
            "spin_connection_gauge_fix_module": gauge["spin_connection_gauge_fix"]["lean_module"],
            "holonomy_quantum_normalized_module": quantum["holonomy_quantum_normalized"]["lean_module"],
            "cycle": "compact singular cycle around Sigma",
            "gauge_fix": "spin connection gauge fixed on the cycle",
            "unit": "holonomy unit chosen by the Z2 orbifold generator",
            "normalized_flux": "flux divided by the holonomy unit is well-defined",
        },
        "logical_arrow": {
            "normalization": "holonomyQuantumNormalizationClosed",
            "flux_law": "fluxQuantizationLawClosed",
            "integer_flux_data": "integerFluxDataClosed",
        },
        "theorem_status": {
            "run10b_holonomy_quantum_normalization_interface_ready": True,
            "normalization_to_flux_law_arrow_formalized": True,
            "run10b_z2_holonomy_unit_interface_ready": True,
            "z2_unit_to_normalization_arrow_formalized": True,
            "spin_connection_gauge_fixed_on_cycle_proved": True,
            "holonomy_unit_chosen_by_orbifold_generator_proved": True,
            "flux_divided_by_holonomy_unit_well_defined": True,
            "holonomy_quantum_normalized_proved": True,
            "normalized_flux_integer_proved": False,
            "full_cosmology_prediction_ready_no_fit": False,
        },
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 EFT RUN 10B Holonomy Quantum Normalization",
        "",
        payload["description"],
        "",
        "## Holonomy Normalization",
    ]
    lines.extend(f"- {key}: {value}" for key, value in payload["holonomy_normalization"].items())
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
