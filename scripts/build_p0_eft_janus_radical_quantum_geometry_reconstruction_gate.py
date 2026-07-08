from __future__ import annotations

import json
from pathlib import Path
from typing import Any


REPORTS = Path("outputs/reports")
JSON_PATH = REPORTS / "p0_eft_janus_radical_quantum_geometry_reconstruction_gate.json"
REPORT_PATH = REPORTS / "p0_eft_janus_radical_quantum_geometry_reconstruction_gate.md"


def build_payload() -> dict[str, Any]:
    return {
        "status": "janus-radical-quantum-geometry-reconstruction",
        "distinction_from_previous_quantum_first": {
            "previous": "quantize or fiber an already classical Sigma/PT throat",
            "radical": "derive Sigma/PT and the Janus geometry as emergent classical data from a primary quantum state space",
            "already_tried": False,
        },
        "required_maps": [
            {
                "id": "state_space",
                "need": "primary Hilbert/coadjoint/TQFT state space",
                "closed": False,
                "blocker": "no published Janus state space with dynamics and inner product",
            },
            {
                "id": "emergent_topology",
                "need": "map from quantum sectors to S4/RP4/PT bridge topology",
                "closed": False,
                "blocker": "CP1/TQFT labels do not by themselves reconstruct the double-sheet topology",
            },
            {
                "id": "emergent_metric",
                "need": "expectation/semiclassical map to scale factor, throat radius, and bimetric fields",
                "closed": False,
                "blocker": "no operator map for a(u), R_s, or g_plus/g_minus",
            },
            {
                "id": "mass_alpha_operator",
                "need": "Hamiltonian/charge operator whose spectrum gives M_bridge and alpha",
                "closed": False,
                "blocker": "same hard blocker as quantum-first, but now moved upstream",
            },
        ],
        "what_this_branch_could_fix": [
            "avoid quantizing an already scale-degenerate classical throat",
            "make topology and alpha consequences of a state sector",
            "turn alpha into an eigenvalue if a boundary Hamiltonian is derived",
        ],
        "what_it_costs": [
            "it is no longer paper-native Janus",
            "it requires a new quantum-geometric postulate or published state-space law",
            "it must rederive the classical Janus limit instead of assuming Sigma",
        ],
        "current_verdict": "not_previously_fully_tried_but_not_closeable_from_current_assets",
        "next_non_rustine_input": "explicit quantum state/action whose semiclassical limit is S4/RP4 plus PT bridge and whose charge spectrum yields alpha",
        "alpha_generated_no_fit": False,
        "gate_passed": True,
    }


def write_reports() -> dict[str, Any]:
    payload = build_payload()
    REPORTS.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Radical Quantum Geometry Reconstruction",
        "",
        "This is distinct from the previous quantum-first branch.",
        "",
        f"Previous: `{payload['distinction_from_previous_quantum_first']['previous']}`",
        f"Radical: `{payload['distinction_from_previous_quantum_first']['radical']}`",
        f"Already fully tried: `{payload['distinction_from_previous_quantum_first']['already_tried']}`",
        "",
        "## Required Maps",
        "",
        "| ID | Need | Closed | Blocker |",
        "|---|---|---:|---|",
        *[
            f"| `{row['id']}` | {row['need']} | `{row['closed']}` | {row['blocker']} |"
            for row in payload["required_maps"]
        ],
        "",
        "## Verdict",
        "",
        payload["current_verdict"],
        "",
        f"Next non-rustine input: `{payload['next_non_rustine_input']}`",
    ]
    REPORT_PATH.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
