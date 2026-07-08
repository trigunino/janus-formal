from __future__ import annotations

import json
from pathlib import Path
from typing import Any


REPORTS = Path("outputs/reports")
JSON_PATH = REPORTS / "p0_eft_janus_bridge_state_law_credible_pistes_terminal_gate.json"
REPORT_PATH = REPORTS / "p0_eft_janus_bridge_state_law_credible_pistes_terminal_gate.md"


def build_payload() -> dict[str, Any]:
    pistes = [
        {
            "id": "composite_boundary_state_law",
            "meaning": "derive alpha internally from Q_bridge, LL flux lattice, and PT primitive state",
            "status": "credible_but_not_closed",
            "terminal_blocker": "no explicit active boundary phase space/action gives all three links",
            "next_if_reopened": "provide null/PT symplectic charge, LL q/F2 units, and PT primitive-sector theorem",
            "no_fit_if_closed": True,
        },
        {
            "id": "alpha_superselection_sector",
            "meaning": "treat alpha like ADM mass: global state label, not local fit",
            "status": "viable_non_no_fit_contract",
            "terminal_blocker": "observations select the sector unless a deeper state law is added",
            "next_if_reopened": "build sector calibration against SN/background data with explicit no no-fit claim",
            "no_fit_if_closed": False,
        },
        {
            "id": "paper_reference_gap_report",
            "meaning": "freeze paper-native Janus and report precisely what the papers fix or leave open",
            "status": "useful_formal_output",
            "terminal_blocker": "paper source set does not derive the missing boundary state law",
            "next_if_reopened": "write reference/gap report comparing published alpha usage to repo contracts",
            "no_fit_if_closed": False,
        },
    ]
    return {
        "status": "janus-bridge-state-law-credible-pistes-terminal",
        "core_verdict": (
            "The remaining credible no-fit route is real but conditional: it needs an "
            "explicit boundary state law. Without it, alpha is a superselection/state sector."
        ),
        "pistes": pistes,
        "rules": {
            "no_direct_alpha_fit": True,
            "no_invented_boundary_law": True,
            "observation_selection_is_not_no_fit": True,
            "paper_reference_is_not_automatic_completion": True,
        },
        "recommended_decision_tree": [
            "If an explicit boundary state law is supplied, reopen composite no-fit closure.",
            "If not, freeze no-fit alpha search as blocked.",
            "Then use alpha as a superselection sector and calibrate observationally.",
            "Maintain a paper-reference gap report to show exactly what was improved or still missing.",
        ],
        "explicit_boundary_state_law_derived": False,
        "alpha_superselection_contract_allowed": True,
        "paper_reference_gap_report_allowed": True,
        "gate_passed": True,
    }


def write_reports() -> dict[str, Any]:
    payload = build_payload()
    REPORTS.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Bridge State Law Credible Pistes Terminal Gate",
        "",
        payload["core_verdict"],
        "",
        "## Pistes",
        "",
        "| ID | Status | Terminal blocker |",
        "|---|---|---|",
        *[
            f"| `{row['id']}` | `{row['status']}` | {row['terminal_blocker']} |"
            for row in payload["pistes"]
        ],
        "",
        "## Decision Tree",
        "",
        *[f"- {step}" for step in payload["recommended_decision_tree"]],
        "",
        f"explicit_boundary_state_law_derived: `{payload['explicit_boundary_state_law_derived']}`",
        f"alpha_superselection_contract_allowed: `{payload['alpha_superselection_contract_allowed']}`",
    ]
    REPORT_PATH.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
