from __future__ import annotations

import json
from pathlib import Path
from typing import Any


REPORTS = Path("outputs/reports")
JSON_PATH = REPORTS / "p0_eft_janus_alpha_superselection_sector_program_gate.json"
REPORT_PATH = REPORTS / "p0_eft_janus_alpha_superselection_sector_program_gate.md"


def build_payload() -> dict[str, Any]:
    return {
        "status": "janus-alpha-superselection-sector-program",
        "physical_interpretation": (
            "alpha is treated as a global state-sector label of the Janus exact "
            "solution, analogous in status to an ADM mass or conserved charge."
        ),
        "alpha_contract": {
            "alpha_is_local_fit_parameter": False,
            "alpha_is_topology_prediction": False,
            "alpha_is_global_state_sector": True,
            "alpha_can_be_observationally_selected": True,
            "full_no_fit_prediction": False,
        },
        "required_state_input": {
            "alpha_m": "positive dimensional scale from state-sector provenance",
            "provenance": "exact_solution_integration_constant_state or published Janus alpha state",
            "forbidden_provenance": ["hidden_fit", "compressed_LCDM", "legacy_Z4", "posthoc_demo"],
        },
        "observational_endpoint": {
            "SN": {
                "role": "relative distance/shape and q0 branch test",
                "breaks_absolute_alpha_scale": False,
            },
            "BAO": {
                "role": "absolute ruler/scale breaking if a native ruler contract is declared",
                "breaks_absolute_alpha_scale": True,
            },
            "Hz": {
                "role": "optional expansion-rate cross-check",
                "breaks_absolute_alpha_scale": "with H0/calibration policy",
            },
            "CMB": {
                "role": "later only, after native background+ruler contract",
                "allowed_now": False,
            },
        },
        "allowed_claims": [
            "Janus exact solution is evaluated as a family of alpha sectors",
            "observations can select or constrain the sector of our universe",
            "the repo records alpha provenance and forbids hidden no-fit promotion",
        ],
        "forbidden_claims": [
            "alpha is predicted by topology alone",
            "alpha is predicted no-fit by current Janus equations",
            "SN-only fixes absolute alpha",
            "CMB validates Janus before native background/ruler closure",
        ],
        "next_executable_step": "build an alpha-sector observational calibration runner using SN+BAO first",
        "program_closed_as_sector_theory": True,
        "needs_new_theory_for_no_fit": True,
        "gate_passed": True,
    }


def write_reports() -> dict[str, Any]:
    payload = build_payload()
    REPORTS.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Alpha Superselection Sector Program",
        "",
        payload["physical_interpretation"],
        "",
        "## Alpha Contract",
        "",
        *[f"- `{k}`: `{v}`" for k, v in payload["alpha_contract"].items()],
        "",
        "## Observational Endpoint",
        "",
        "| Layer | Role | Breaks absolute alpha scale |",
        "|---|---|---:|",
        *[
            f"| `{key}` | {row['role']} | `{row.get('breaks_absolute_alpha_scale', row.get('allowed_now'))}` |"
            for key, row in payload["observational_endpoint"].items()
        ],
        "",
        "## Allowed Claims",
        "",
        *[f"- {claim}" for claim in payload["allowed_claims"]],
        "",
        "## Forbidden Claims",
        "",
        *[f"- {claim}" for claim in payload["forbidden_claims"]],
        "",
        f"Next executable step: `{payload['next_executable_step']}`",
    ]
    REPORT_PATH.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
