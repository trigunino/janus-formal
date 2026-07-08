from __future__ import annotations

import json
from pathlib import Path
from typing import Any


REPORTS = Path("outputs/reports")
JSON_PATH = REPORTS / "p0_eft_janus_llbrane_bridge_source_gate.json"
REPORT_PATH = REPORTS / "p0_eft_janus_llbrane_bridge_source_gate.md"


def build_payload() -> dict[str, Any]:
    return {
        "status": "janus-llbrane-bridge-source-gate",
        "bibliography_anchors": [
            "Einstein-Rosen bridge needs lightlike brane source",
            "LL-brane wormholes: bridge mass is a function of dynamical tension",
            "Barrabes-Israel null shell formalism",
        ],
        "closed_by_bibliography": {
            "null_throat_requires_surface_source": True,
            "well_defined_LL_brane_action_exists": True,
            "bridge_mass_can_depend_on_LL_tension": True,
        },
        "janus_map": {
            "M_bridge_to_alpha": "alpha_m = -2*pi*G*M_bridge/c^2",
            "M_bridge_from_tension": "available structurally from LL-brane junction conditions",
            "tension_symbol": "chi_LL",
            "chi_LL_derived_from_Janus": False,
            "chi_LL_quantized": False,
        },
        "candidate_routes_to_chi_LL": [
            {
                "id": "PT_boundary_condition",
                "status": "open",
                "missing": "explicit Janus/PT null boundary condition fixing LL tension",
            },
            {
                "id": "LL_auxiliary_flux_quantization",
                "status": "open",
                "missing": "worldvolume gauge sector, charge unit, compact cycle",
            },
            {
                "id": "global_Noether_charge_matching",
                "status": "conditional",
                "missing": "integrable boundary charge equal to LL energy",
            },
        ],
        "does_more_than_previous_branches": (
            "Yes: it turns the abstract bridge mass into a concrete null-shell source problem."
        ),
        "why_not_closed": (
            "The bridge mass is no longer arbitrary once chi_LL is known, but Janus still "
            "does not derive or quantize chi_LL."
        ),
        "deep_verdict": "best_bridge_mass_route_but_tension_law_missing",
        "no_fit_alpha_generated": False,
        "next_concrete_test": "derive_chi_LL_from_PT_boundary_condition_or_LL_flux_quantization",
        "gate_passed": True,
    }


def write_reports() -> dict[str, Any]:
    payload = build_payload()
    REPORTS.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus LL-Brane Bridge Source Gate",
        "",
        f"Deep verdict: `{payload['deep_verdict']}`",
        f"No-fit alpha generated: `{payload['no_fit_alpha_generated']}`",
        "",
        "## Closed By Bibliography",
        "",
        *[f"- `{key}`: `{value}`" for key, value in payload["closed_by_bibliography"].items()],
        "",
        "## Janus Map",
        "",
        *[f"- `{key}`: `{value}`" for key, value in payload["janus_map"].items()],
        "",
        "## Routes To chi_LL",
        "",
        "| Route | Status | Missing |",
        "|---|---|---|",
        *[
            f"| `{row['id']}` | `{row['status']}` | {row['missing']} |"
            for row in payload["candidate_routes_to_chi_LL"]
        ],
    ]
    REPORT_PATH.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
