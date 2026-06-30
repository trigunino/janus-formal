from __future__ import annotations

from pathlib import Path
import json
import sys

if __package__ in (None, ""):
    sys.path.append(str(Path(__file__).resolve().parents[1]))

REPORT_PATH = Path("outputs/reports/p0_eft_run10b_spin_connection_gauge_fix.md")
JSON_PATH = Path("outputs/reports/p0_eft_run10b_spin_connection_gauge_fix.json")


def build_payload() -> dict:
    return {
        "description": "RUN 10B phase 8: spin-connection gauge fix on the singular cycle.",
        "frozen_sectors": {
            "growth_solver": "read-only",
            "sdss_eboss_data": "read-only",
            "holst_membrane_fit": "read-only",
        },
        "spin_connection_gauge_fix": {
            "lean_module": "P0EFTOrbifoldSpinConnectionGaugeFix",
            "cycle": "compact singular cycle around Sigma",
            "restriction": "spin connection restricts to the orbifold cycle",
            "gauge": "gauge representative chosen on the cycle",
        },
        "logical_arrow": {
            "gauge_fix": "spinConnectionGaugeFixedOnCycle",
            "normalization": "holonomyQuantumNormalizationClosed",
            "flux_law": "fluxQuantizationLawClosed",
        },
        "theorem_status": {
            "run10b_spin_connection_gauge_fix_ready": True,
            "spin_connection_gauge_fixed_on_cycle_proved": True,
            "spin_connection_restricts_to_orbifold_cycle_proved": True,
            "holonomy_quantum_normalized_proved": False,
            "normalized_flux_integer_proved": False,
            "full_cosmology_prediction_ready_no_fit": False,
        },
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 EFT RUN 10B Spin Connection Gauge Fix",
        "",
        payload["description"],
        "",
        "## Spin Connection Gauge Fix",
    ]
    lines.extend(f"- {key}: {value}" for key, value in payload["spin_connection_gauge_fix"].items())
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
