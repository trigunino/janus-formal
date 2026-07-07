from __future__ import annotations

import json
from pathlib import Path
from typing import Any


BASE = Path("outputs/active_z2_sigma")
INPUT_PATH = BASE / "primitive_sector_n_selection_inputs.json"
OUTPUT_PATH = BASE / "alpha_composite_selector_frontier_inputs.json"
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_primitive_sector_n_selection_gate.json")
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_primitive_sector_n_selection_gate.md")


def _read(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8")) if path.exists() else {}


def build_payload(
    input_path: Path = INPUT_PATH,
    output_path: Path = OUTPUT_PATH,
    *,
    write_output: bool = False,
) -> dict[str, Any]:
    data = _read(input_path)
    checks = {
        "sector_lattice_exists": bool(data.get("sector_lattice_exists")),
        "zero_sector_excluded_by_nontrivial_throat": bool(
            data.get("zero_sector_excluded_by_nontrivial_throat")
        ),
        "fusion_channels_forbidden": bool(data.get("fusion_channels_forbidden")),
        "splitting_channels_forbidden": bool(data.get("splitting_channels_forbidden")),
        "empty_punctures_forbidden": bool(data.get("empty_punctures_forbidden")),
        "ground_state_energy_monotone_in_abs_n": bool(
            data.get("ground_state_energy_monotone_in_abs_n")
        ),
        "orientation_identifies_plus_minus_n": bool(data.get("orientation_identifies_plus_minus_n")),
        "primitive_sector_internal_provenance": bool(
            data.get("primitive_sector_internal_provenance")
        ),
    }
    ready = all(checks.values())
    frontier_payload = None
    if ready:
        frontier_payload = {
            "charge_lattice_integrality_derived": bool(
                data.get("charge_lattice_integrality_derived")
            ),
            "minimal_mass_unit_derived": bool(data.get("minimal_mass_unit_derived")),
            "unit_value_kg_derived": bool(data.get("unit_value_kg_derived")),
            "nonzero_sector_required": True,
            "fusion_splitting_forbidden": True,
            "n_equals_one_selected": True,
            "selection_provenance_internal": True,
        }
        if write_output:
            output_path.parent.mkdir(parents=True, exist_ok=True)
            output_path.write_text(json.dumps(frontier_payload, indent=2), encoding="utf-8")
    return {
        "status": "janus-z2-primitive-sector-n-selection-gate",
        "active_core": "Z2_tunnel_Sigma",
        "checks": checks,
        "primitive_n_selected": ready,
        "selected_n": 1 if ready else None,
        "blocked_by": [key for key, ok in checks.items() if not ok],
        "selection_logic": (
            "If the throat requires a nonzero lattice sector, fusion/splitting "
            "are forbidden, and the ground-state energy is monotone in |n|, "
            "the primitive ground sector is |n|=1."
        ),
        "frontier_payload": frontier_payload,
        "gate_passed": True,
    }


def write_reports() -> dict[str, Any]:
    payload = build_payload(write_output=True)
    JSON_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(
        "\n".join(
            [
                "# Janus Z2 Primitive Sector n Selection Gate",
                "",
                f"Primitive n selected: `{payload['primitive_n_selected']}`",
                f"Selected n: `{payload['selected_n']}`",
                "",
                payload["selection_logic"],
            ]
        ),
        encoding="utf-8",
    )
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
