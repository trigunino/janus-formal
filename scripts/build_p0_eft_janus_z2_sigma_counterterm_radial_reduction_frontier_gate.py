from __future__ import annotations

import json
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from scripts.build_p0_eft_janus_z2_sigma_counterterm_density_expansion_gate import (
    build_payload as build_density_expansion_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_counterterm_local_density_basis_gate import (
    build_payload as build_local_density_basis_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_counterterm_radial_block_gate import (
    build_payload as build_radial_block_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_counterterm_residual_extraction_gate import (
    build_payload as build_residual_extraction_payload,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_counterterm_radial_reduction_frontier_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_counterterm_radial_reduction_frontier_gate.json")


def _first_blocker(*payloads: dict) -> str:
    for payload in payloads:
        blocker = payload.get("primary_blocker")
        if blocker and blocker != "none":
            return blocker
    return "counterterm_residual_exact_primitive_and_radial_reduction"


def build_payload() -> dict:
    residual = build_residual_extraction_payload()
    basis = build_local_density_basis_payload()
    density = build_density_expansion_payload()
    radial = build_radial_block_payload()
    declared = {
        "counterterm_radial_block_imported": True,
        "residual_extraction_gate_imported": True,
        "density_expansion_gate_imported": True,
        "boundary_counterterm_bibliography_checked": True,
        "reduction_chain_declared": True,
        "no_fitted_counterterm_coefficient": True,
    }
    chain = {
        "residual_one_form_explicit": residual["closure"]["residual_one_form_explicit"],
        "residual_integrability_proved": residual["closure"]["residual_integrability_proved"],
        "counterterm_primitive_integrated": residual["closure"]["counterterm_primitive_integrated"],
        "local_density_basis_complete": basis["closure"]["local_density_basis_complete"],
        "L_ct_local_expansion_derived": density["closure"]["L_ct_expanded_in_active_variables"],
        "L_ct_ready_for_radial_variation": density["closure"]["L_ct_ready_for_radial_variation"],
        "E_counterterm_radial_block_reduced": radial["closure"]["E_counterterm_radial_block_reduced"],
        "counterterm_block_reduced": radial["counterterm_radial_block_reduced"],
    }
    ready = all(declared.values()) and all(chain.values())
    primary_blocker = "none" if ready else _first_blocker(residual, density, radial, basis)
    return {
        "status": "janus-z2-sigma-counterterm-radial-reduction-frontier-gate",
        "active_core": "Z2_tunnel_Sigma",
        "primary_sources_checked": [
            "Brown-York boundary stress/counterterm method",
            "Balasubramanian-Kraus boundary counterterm stress tensor",
            "covariant phase space / variational bicomplex boundary exactness",
            "active Janus Sigma nonlinear residual closure gate",
        ],
        "source_links": [
            "https://arxiv.org/abs/hep-th/9902121",
            "https://arxiv.org/abs/gr-qc/9209012",
            "https://arxiv.org/abs/1806.01529",
        ],
        "bibliography_result": (
            "Standard boundary counterterm and variational-bicomplex methods justify the "
            "chain residual one-form -> exactness -> primitive -> local density -> radial "
            "variation. They do not provide the active Janus/Sigma residual coefficients."
        ),
        "declared": declared,
        "chain": chain,
        "upstream_frontiers": {
            "residual_extraction": {
                "gate": residual["status"],
                "ready": residual["counterterm_residual_extraction_ready"],
                "closure": residual["closure"],
                "primary_blocker": residual.get("primary_blocker", "counterterm_residual_extraction"),
            },
            "local_density_basis": {
                "gate": basis["status"],
                "ready": basis["counterterm_local_density_basis_ready"],
                "closure": basis["closure"],
                "primary_blocker": basis.get("primary_blocker", "counterterm_local_density_basis"),
            },
            "density_expansion": {
                "gate": density["status"],
                "ready": density["counterterm_density_expansion_ready"],
                "closure": density["closure"],
                "primary_blocker": density.get("primary_blocker", "counterterm_density_expansion"),
            },
            "radial_block": {
                "gate": radial["status"],
                "block_reduced": radial["counterterm_radial_block_reduced"],
                "closure": radial["closure"],
                "primary_blocker": radial.get("primary_blocker", "counterterm_radial_block"),
            },
        },
        "reduction_chain": [
            "alpha_res explicit",
            "d_field alpha_res = 0",
            "S_ct primitive integrated",
            "L_ct expanded in active local density basis",
            "delta_RSigma integral_Sigma sqrt(|h|) L_ct reduced",
        ],
        "counterterm_radial_reduction_frontier_ledger_declared": all(declared.values()),
        "counterterm_radial_reduction_ready": ready,
        "gate_passed": ready,
        "primary_blocker": primary_blocker,
        "current_frontier": [
            f"{key} = false"
            for key, ready in chain.items()
            if not ready and key != "counterterm_block_reduced"
        ],
        "next_required": [
            "close_counterterm_residual_one_form_decomposition_gate",
            "close_counterterm_residual_integrability_gate",
            "integrate_counterterm_primitive",
            "close_counterterm_density_expansion_gate",
            "reduce_E_counterterm_radial_block",
            "feed_counterterm_block_reduced_to_throat_radius_solution_frontier",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Counterterm Radial Reduction Frontier Gate",
        "",
        f"Active core: `{payload['active_core']}`",
        f"Ledger declared: `{payload['counterterm_radial_reduction_frontier_ledger_declared']}`",
        f"Reduction ready: `{payload['counterterm_radial_reduction_ready']}`",
        "",
        "## Reduction Chain",
    ]
    lines.extend(f"- `{item}`" for item in payload["reduction_chain"])
    lines.extend(["", "## Current Frontier"])
    lines.extend(f"- `{item}`" for item in payload["current_frontier"])
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
