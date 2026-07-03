from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_throat_radius_block_expansion_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_throat_radius_block_expansion_gate.json")


def build_payload() -> dict:
    declared = {
        "Israel_shell_bibliography_checked": True,
        "GHY_Brown_York_bibliography_checked": True,
        "radial_equation_declared": True,
        "Cartan_GHY_radial_block_declared": True,
        "Holst_Nieh_Yan_radial_block_declared": True,
        "matter_flux_radial_block_declared": True,
        "tunnel_junction_radial_block_declared": True,
        "counterterm_radial_block_declared": True,
        "no_observational_radius_fit": True,
        "E_RSigma_block_sum_declared": True,
    }
    reduced = {
        "Cartan_GHY_radial_block_reduced": True,
        "Holst_Nieh_Yan_radial_block_reduced": True,
        "matter_flux_radial_block_reduced": False,
        "tunnel_junction_radial_block_reduced": True,
        "counterterm_radial_block_reduced": False,
        "E_RSigma_expanded": False,
        "E_RSigma_solved": False,
        "R_Sigma_of_a_ready": False,
    }
    return {
        "status": "janus-z2-sigma-throat-radius-block-expansion-gate",
        "active_core": "Z2_tunnel_Sigma",
        "primary_sources_checked": [
            "Israel 1966, Singular hypersurfaces and thin shells in general relativity",
            "York/Gibbons-Hawking boundary variational term",
            "Brown-York quasilocal boundary stress",
            "Darmois-Israel dynamic thin-shell wormhole equation-of-motion literature",
        ],
        "bibliography_result": (
            "Generic sources justify reducing the radial shell equation as a sum of "
            "boundary-action blocks. They do not provide the Janus-specific block "
            "reductions for the resolved Sigma throat."
        ),
        "declared": declared,
        "reduced": reduced,
        "block_sum": (
            "E_RSigma = E_CartanGHY + E_HolstNiehYan + E_matterFlux "
            "+ E_tunnelJunction + E_counterterm = 0"
        ),
        "throat_radius_block_ledger_declared": all(declared.values()),
        "all_radial_blocks_reduced": all(
            reduced[key]
            for key in [
                "Cartan_GHY_radial_block_reduced",
                "Holst_Nieh_Yan_radial_block_reduced",
                "matter_flux_radial_block_reduced",
                "tunnel_junction_radial_block_reduced",
                "counterterm_radial_block_reduced",
            ]
        ),
        "throat_radius_block_expansion_ready": all(declared.values())
        and reduced["E_RSigma_expanded"],
        "throat_radius_solved_from_blocks": all(declared.values()) and all(reduced.values()),
        "next_required": [
            "reduce_matter_flux_radial_block_E_flux",
            "reduce_counterterm_radial_block_E_ct",
            "solve_E_RSigma_equals_zero_for_R_Sigma_of_a",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Throat Radius Block Expansion Gate",
        "",
        f"Active core: `{payload['active_core']}`",
        f"Ledger declared: `{payload['throat_radius_block_ledger_declared']}`",
        f"Expansion ready: `{payload['throat_radius_block_expansion_ready']}`",
        f"Solved from blocks: `{payload['throat_radius_solved_from_blocks']}`",
        "",
        "## Block Sum",
        f"`{payload['block_sum']}`",
        "",
        "## Next Required",
    ]
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
