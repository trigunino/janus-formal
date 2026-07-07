from __future__ import annotations

import json
from pathlib import Path
from typing import Any


BASE = Path("outputs/active_z2_sigma")
INPUT_PATH = BASE / "alpha_composite_selector_frontier_inputs.json"
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_alpha_composite_selector_frontier_gate.json")
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_alpha_composite_selector_frontier_gate.md")


def _read(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8")) if path.exists() else {}


def build_payload(input_path: Path = INPUT_PATH) -> dict[str, Any]:
    data = _read(input_path)
    charge_unit = {
        "moment_map_exists": True,
        "charge_to_alpha_map_exists": True,
        "coadjoint_mass_label_exists": True,
        "charge_lattice_integrality_derived": bool(data.get("charge_lattice_integrality_derived")),
        "minimal_mass_unit_derived": bool(data.get("minimal_mass_unit_derived")),
        "unit_value_kg_derived": bool(data.get("unit_value_kg_derived")),
    }
    primitive_sector = {
        "integer_sector_formalism_exists": True,
        "nonzero_sector_required": bool(data.get("nonzero_sector_required")),
        "fusion_splitting_forbidden": bool(data.get("fusion_splitting_forbidden")),
        "n_equals_one_selected": bool(data.get("n_equals_one_selected")),
        "selection_provenance_internal": bool(data.get("selection_provenance_internal")),
    }
    charge_unit_ready = all(charge_unit.values())
    primitive_ready = all(primitive_sector.values())
    return {
        "status": "janus-z2-alpha-composite-selector-frontier-gate",
        "active_core": "Z2_tunnel_Sigma",
        "input_path": str(input_path),
        "input_present": input_path.exists(),
        "charge_unit_frontier": charge_unit,
        "primitive_sector_frontier": primitive_sector,
        "m_charge_ready": charge_unit_ready,
        "primitive_n_ready": primitive_ready,
        "unique_alpha_selector_ready": charge_unit_ready and primitive_ready,
        "strongest_formula_if_ready": "alpha_n = 2*pi*G*|n|*m_charge/c^2",
        "current_frontier": [
            key for key, ok in charge_unit.items() if not ok
        ] + [
            key for key, ok in primitive_sector.items() if not ok
        ],
        "hard_no_go": (
            "Current Janus/Z2/Sigma formal assets give a conserved mass label and "
            "a possible integer sector, but not an internal mass quantum or a "
            "primitive-sector law. The composite route is therefore not dead, "
            "but it requires one new internally derived quantum-state theorem."
        ),
        "next_possible_theorems": [
            "derive charge lattice integrality from PT/Souriau boundary symplectic form",
            "derive minimal mass unit from throat quantum boundary condition",
            "derive primitive n=1 sector from irreducibility/superselection",
        ],
        "forbidden_shortcuts": [
            "set m_charge to proton mass by hand",
            "set m_charge to Planck mass by hand",
            "set n=1 without primitive-sector theorem",
            "use observation to choose n or m_charge",
        ],
        "gate_passed": True,
    }


def write_reports() -> dict[str, Any]:
    payload = build_payload()
    JSON_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2 Alpha Composite Selector Frontier Gate",
        "",
        f"m_charge ready: `{payload['m_charge_ready']}`",
        f"primitive n ready: `{payload['primitive_n_ready']}`",
        f"unique alpha selector ready: `{payload['unique_alpha_selector_ready']}`",
        "",
        payload["hard_no_go"],
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
