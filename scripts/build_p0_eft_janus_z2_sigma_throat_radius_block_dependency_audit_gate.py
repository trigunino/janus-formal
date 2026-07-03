from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_throat_radius_block_dependency_audit_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_throat_radius_block_dependency_audit_gate.json")


def build_payload() -> dict:
    declared = {
        "throat_radius_block_expansion_gate_declared": True,
        "matter_flux_radial_block_gate_declared": True,
        "counterterm_radial_block_gate_declared": True,
        "counterterm_density_expansion_gate_declared": True,
    }
    reduced = {
        "Cartan_GHY_block_reduced": True,
        "Holst_Nieh_Yan_block_reduced": True,
        "tunnel_junction_block_reduced": True,
        "matter_flux_block_reduced": False,
        "counterterm_block_reduced": False,
    }
    allowed = {
        "E_RSigma_expansion_allowed": False,
        "R_Sigma_solution_allowed": False,
    }
    return {
        "status": "janus-z2-sigma-throat-radius-block-dependency-audit-gate",
        "active_core": "Z2_tunnel_Sigma",
        "primary_sources_checked": [
            "Israel shell equation radial block decomposition",
            "thin-shell flux conservation terms",
            "Brown-York/counterterm boundary variation literature",
            "active Janus radial block gates",
        ],
        "bibliography_result": (
            "The decomposition into radial blocks is standard. Current Janus status "
            "shows three structural blocks reduced, while matter-flux and counterterm "
            "blocks still block E_RSigma expansion and R_Sigma(a)."
        ),
        "declared": declared,
        "reduced": reduced,
        "allowed": allowed,
        "missing_blocks": [
            "matter_flux_block_reduced",
            "counterterm_block_reduced",
        ],
        "throat_radius_block_dependencies_declared": all(declared.values()),
        "missing_radius_blocks_closed": all(
            reduced[key] for key in ["matter_flux_block_reduced", "counterterm_block_reduced"]
        ),
        "throat_radius_block_dependency_ready": all(declared.values())
        and all(reduced.values())
        and all(allowed.values()),
        "next_required": [
            "close_matter_flux_radial_block_gate",
            "close_counterterm_density_expansion_gate",
            "close_counterterm_radial_block_gate",
            "then_expand_E_RSigma",
            "then_solve_R_Sigma_of_a",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Throat Radius Block Dependency Audit Gate",
        "",
        f"Active core: `{payload['active_core']}`",
        f"Dependencies declared: `{payload['throat_radius_block_dependencies_declared']}`",
        f"Missing blocks closed: `{payload['missing_radius_blocks_closed']}`",
        f"Ready: `{payload['throat_radius_block_dependency_ready']}`",
        "",
        "## Missing Blocks",
    ]
    lines.extend(f"- `{item}`" for item in payload["missing_blocks"])
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
