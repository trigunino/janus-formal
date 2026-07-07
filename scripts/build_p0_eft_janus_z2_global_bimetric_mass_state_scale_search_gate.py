from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_global_bimetric_mass_state_scale_search_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_global_bimetric_mass_state_scale_search_gate.json"
)


def build_payload() -> dict:
    routes = {
        "exact_time_dependent_bimetric_solution": {
            "search_target": "integration constant / generalized conserved energy",
            "scale_found": False,
            "next_required": "derive conserved charge in dimensional units",
        },
        "bimetric_compact_object_solution": {
            "search_target": "Schwarzschild/TOV mass parameter from active source",
            "scale_found": False,
            "next_required": "derive active source mass parameter, not observational mass",
        },
        "Noether_Souriau_global_state": {
            "search_target": "global Hamiltonian/Noether charge fixing bridge state",
            "scale_found": False,
            "next_required": "derive state-selection law for the charge",
        },
        "early_universe_state": {
            "search_target": "occupation/particle number setting a mass scale",
            "scale_found": False,
            "next_required": "derive N_occ and mass unit from action/state",
        },
        "topology_only": {
            "search_target": "S4/RP4/Z2 projective topology",
            "scale_found": False,
            "next_required": "topology fixes ratios only, not absolute length",
        },
    }
    return {
        "status": "janus-z2-global-bimetric-mass-state-scale-search-gate",
        "active_core": "Z2_tunnel_Sigma",
        "purpose": "search for an absolute mass/state scale outside the null throat",
        "routes": routes,
        "any_global_scale_found": any(route["scale_found"] for route in routes.values()),
        "best_next_routes": [
            "exact_time_dependent_bimetric_solution",
            "Noether_Souriau_global_state",
            "bimetric_compact_object_solution",
        ],
        "interpretation": (
            "The global bimetric/cosmological model is the right place to look for "
            "an absolute state scale. Current repo data still expose only targets, "
            "not a derived mass or length. Topology alone remains scale-free."
        ),
        "gate_passed": False,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2 Global Bimetric Mass/State Scale Search Gate",
        "",
        payload["interpretation"],
        "",
        f"Any global scale found: `{payload['any_global_scale_found']}`",
        "",
        "## Best Next Routes",
    ]
    lines.extend(f"- `{item}`" for item in payload["best_next_routes"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
