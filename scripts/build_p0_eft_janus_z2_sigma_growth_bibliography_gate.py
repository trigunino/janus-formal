from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_growth_bibliography_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_growth_bibliography_gate.json")


def build_payload() -> dict:
    sources = {
        "standard_linear_perturbations": {
            "url": "https://arxiv.org/abs/astro-ph/9506072",
            "supports": ["linear_scalar_perturbation_framework", "Boltzmann_hierarchy_context"],
        },
        "einstein_cartan_perturbations": {
            "url": "https://arxiv.org/abs/gr-qc/0202022",
            "supports": ["metric_perturbations_with_torsion_context"],
        },
        "bimetric_growth_context": {
            "url": "https://link.aps.org/doi/10.1103/PhysRevD.82.043523",
            "supports": ["bimetric_fluctuation_growth_context"],
        },
        "janus_2024_structure_context": {
            "url": "https://arxiv.org/abs/2412.04644",
            "supports": ["two_metric_large_structure_claims", "positive_negative_mass_interaction_context"],
        },
    }
    return {
        "status": "janus-z2-sigma-growth-bibliography-gate",
        "active_core": "Z2_tunnel_Sigma",
        "sources": sources,
        "standard_linear_perturbation_source_found": True,
        "bimetric_perturbation_source_found": True,
        "einstein_cartan_perturbation_source_found": True,
        "janus_structure_growth_source_found": True,
        "complete_z2_sigma_growth_equations_found": False,
        "local_growth_derivation_required": True,
        "may_import_standard_scalar_perturbation_framework": True,
        "must_derive_z2_sigma_mu_slip_friction_locally": True,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Growth Bibliography Gate",
        "",
        f"Active core: `{payload['active_core']}`",
        f"Complete Z2/Sigma growth equations found: `{payload['complete_z2_sigma_growth_equations_found']}`",
        f"Local derivation required: `{payload['local_growth_derivation_required']}`",
        "",
        "## Sources",
    ]
    for name, row in payload["sources"].items():
        lines.append(f"- `{name}`: {row['url']}")
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
