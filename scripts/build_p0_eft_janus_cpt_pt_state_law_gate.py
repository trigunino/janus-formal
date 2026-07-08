from __future__ import annotations

import json
from pathlib import Path
from typing import Any


REPORTS = Path("outputs/reports")
JSON_PATH = REPORTS / "p0_eft_janus_cpt_pt_state_law_gate.json"
REPORT_PATH = REPORTS / "p0_eft_janus_cpt_pt_state_law_gate.md"


def build_payload() -> dict[str, Any]:
    mechanisms = [
        {
            "id": "boyle_finn_turok_preferred_vacuum",
            "input": "CPT-invariant pre/post-bang spacetime",
            "output": "preferred QFT vacuum and right-handed-neutrino dark-matter mechanism",
            "alpha_relevance": "state selection exists, but not a gravitational alpha value",
            "closes_alpha": False,
        },
        {
            "id": "janus_pt_two_sheet_vacuum",
            "input": "Janus PT pairing between sheets/throat",
            "output": "candidate no-free-initial-state principle",
            "alpha_relevance": "could fix alpha only if vacuum energy or bridge charge is computed",
            "closes_alpha": False,
        },
        {
            "id": "sakharov_twin_universe_interpretation",
            "input": "matter/antimatter or positive/negative sector pairing",
            "output": "global symmetry interpretation",
            "alpha_relevance": "does not by itself set a scale",
            "closes_alpha": False,
        },
    ]
    return {
        "status": "janus-cpt-pt-state-law-gate",
        "bibliography_anchors": [
            "Boyle-Finn-Turok CPT-symmetric universe",
            "Big Bang CPT and neutrino dark matter",
            "Sakharov twin-universe CPT idea",
        ],
        "mechanisms": mechanisms,
        "closed_by_bibliography": {
            "pt_cpt_can_select_preferred_vacuum": True,
            "pt_cpt_can_predict_some_particle_content": True,
        },
        "not_closed_for_janus": {
            "janus_field_content_in_quantum_state": False,
            "vacuum_energy_density_computed": False,
            "M_bridge_from_state_computed": False,
            "alpha_from_state_no_fit": False,
        },
        "required_derivation": [
            "define the Janus/PT quantum field content on both sheets",
            "construct the PT/CPT invariant vacuum on the resolved throat background",
            "renormalize the vacuum energy or boundary charge with a Janus reference",
            "prove that the resulting energy maps to M_bridge/alpha",
        ],
        "world_interpretation_if_completed": (
            "alpha would be fixed by the unique globally PT/CPT-symmetric quantum state, "
            "not by late-time observational fitting."
        ),
        "deep_verdict": "promising_state_principle_but_no_alpha_energy_yet",
        "no_fit_alpha_generated": False,
        "next_concrete_test": "construct_Janus_PT_vacuum_energy_functional_or_reject_missing_field_content",
        "gate_passed": True,
    }


def write_reports() -> dict[str, Any]:
    payload = build_payload()
    REPORTS.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus CPT/PT State-Law Gate",
        "",
        f"Deep verdict: `{payload['deep_verdict']}`",
        f"No-fit alpha generated: `{payload['no_fit_alpha_generated']}`",
        "",
        "## Mechanisms",
        "",
        "| Mechanism | Closes alpha | Relevance |",
        "|---|---:|---|",
        *[
            f"| `{row['id']}` | `{row['closes_alpha']}` | {row['alpha_relevance']} |"
            for row in payload["mechanisms"]
        ],
        "",
        "## Required Derivation",
        "",
        *[f"- {item}" for item in payload["required_derivation"]],
    ]
    REPORT_PATH.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
