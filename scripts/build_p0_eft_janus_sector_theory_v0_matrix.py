from __future__ import annotations

import json
from pathlib import Path
from typing import Any


REPORTS = Path("outputs/reports")
JSON_PATH = REPORTS / "p0_eft_janus_sector_theory_v0_matrix.json"
REPORT_PATH = REPORTS / "p0_eft_janus_sector_theory_v0_matrix.md"


SECTOR_LAWS: list[dict[str, Any]] = [
    {
        "id": "published_sn_q0_sector",
        "world_interpretation": "Janus exact expansion sector selected by the published SN shape parameter.",
        "predicts_q0_no_fit": False,
        "testable_now": True,
        "q0": -0.087,
        "status": "paper_anchored_observation_sector",
    },
    {
        "id": "primitive_topology_sector",
        "world_interpretation": "Pure S4/RP4 + resolved Sigma topology fixes ratios/cycles, not a cosmic energy scale.",
        "predicts_q0_no_fit": False,
        "testable_now": False,
        "q0": None,
        "status": "under_determined",
    },
    {
        "id": "quantum_cp1_spin_sector",
        "world_interpretation": "Boundary Hilbert labels exist, but no Janus mass operator maps spin label to alpha.",
        "predicts_q0_no_fit": False,
        "testable_now": False,
        "q0": None,
        "status": "discrete_labels_without_energy_scale",
    },
    {
        "id": "asymptotic_null_charge_sector",
        "world_interpretation": "Would make alpha a boundary energy charge if Janus supplies a real null/asymptotic charge.",
        "predicts_q0_no_fit": False,
        "testable_now": False,
        "q0": None,
        "status": "conditional_charge_missing",
    },
    {
        "id": "observation_selected_q0_sector",
        "world_interpretation": "The universe occupies one continuous Janus energy sector, selected by data like an ADM mass.",
        "predicts_q0_no_fit": False,
        "testable_now": True,
        "q0": "grid",
        "status": "viable_not_no_fit",
    },
]


def build_payload() -> dict[str, Any]:
    return {
        "status": "janus-sector-theory-v0-matrix",
        "sector_laws": SECTOR_LAWS,
        "sector_law_count": len(SECTOR_LAWS),
        "no_fit_alpha_generated": False,
        "magic_fit_forbidden": True,
        "allowed_fit_policy": {
            "profile_SN_offset": True,
            "profile_BAO_scale": True,
            "fit_alpha_directly": False,
            "interpret_q0_grid_as_sector_selection": True,
        },
        "next_observation_test": "SN_full_cov_plus_BAO_existing_gate",
        "gate_passed": True,
    }


def write_reports() -> dict[str, Any]:
    payload = build_payload()
    REPORTS.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Sector Theory v0 Matrix",
        "",
        f"No-fit alpha generated: `{payload['no_fit_alpha_generated']}`",
        f"Magic fit forbidden: `{payload['magic_fit_forbidden']}`",
        "",
        "| Sector law | Testable now | Status |",
        "|---|---:|---|",
        *[
            f"| `{row['id']}` | `{row['testable_now']}` | `{row['status']}` |"
            for row in payload["sector_laws"]
        ],
    ]
    REPORT_PATH.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
