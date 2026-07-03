from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_normal_matter_current_readiness_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_normal_matter_current_readiness_gate.json")


def build_payload() -> dict:
    declared = {
        "normal_matter_current_gate_imported": True,
        "plus_minus_matter_current_gate_imported": True,
        "projected_Dirac_matter_current_gate_imported": True,
        "projected_Dirac_normal_current_gate_imported": True,
        "active_embedding_readiness_gate_imported": True,
        "Dirac_Noether_current_bibliography_checked": True,
    }
    readiness = {
        "active_embedding_ready": False,
        "Sigma_normals_ready": False,
        "plus_minus_matter_currents_ready": False,
        "projected_Dirac_matter_current_ready": False,
        "projected_Dirac_normal_current_ready": False,
        "no_normal_matter_current_derived": False,
        "no_normal_matter_current_ready": False,
    }
    return {
        "status": "janus-z2-sigma-normal-matter-current-readiness-gate",
        "active_core": "Z2_tunnel_Sigma",
        "primary_sources_checked": [
            "Dirac U(1) Noether current",
            "curved-spacetime Dirac equation with tetrad/spin connection",
            "thin-shell normal-flux projection",
        ],
        "source_links": [
            "https://arxiv.org/html/2503.03918v2",
            "https://s3.cern.ch/inspire-prod-files-d/d0a75bfac1295febe61b60f90aef7505",
            "https://doi.org/10.1007/BF02710419",
        ],
        "bibliography_result": (
            "Generic Dirac theory supplies J^mu = psibar gamma^mu psi and its "
            "normal projection. Janus Z2/Sigma still needs the active projected "
            "current and active Sigma normals before J_n^Z2Sigma can be tested."
        ),
        "declared": declared,
        "readiness": readiness,
        "formulae": {
            "dirac_current": "J_pm^mu = psibar_pm gamma_pm^mu psi_pm",
            "normal_projection": "J_n^pm = J_pm^mu n_mu^pm",
            "z2_current": "J_n^Z2Sigma = J_n^+ + eps_Z2 J_n^-",
            "transparency_test": "J_n^Z2Sigma = 0",
        },
        "closed": [
            "Dirac_Noether_current_formula_declared",
            "normal_projection_formula_declared",
        ],
        "still_open": [
            "active_embedding_ready",
            "Sigma_normals_ready",
            "plus_minus_matter_currents_ready",
            "projected_Dirac_matter_current_ready",
            "projected_Dirac_normal_current_ready",
            "no_normal_matter_current_derived",
        ],
        "normal_matter_current_readiness_ledger_declared": all(declared.values()),
        "normal_matter_current_readiness_ready": all(declared.values()) and all(readiness.values()),
        "next_required": [
            "close_active_embedding_readiness_gate",
            "close_projected_Dirac_matter_current_gate",
            "project_currents_on_active_Sigma_normals",
            "prove_or_reject_J_n_Z2Sigma_equals_zero",
            "feed_no_normal_current_to_transparency_readiness_gate",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Normal Matter Current Readiness Gate",
        "",
        f"Active core: `{payload['active_core']}`",
        f"Ledger declared: `{payload['normal_matter_current_readiness_ledger_declared']}`",
        f"Readiness ready: `{payload['normal_matter_current_readiness_ready']}`",
        "",
        "## Formulae",
    ]
    lines.extend(f"- `{key}`: `{value}`" for key, value in payload["formulae"].items())
    lines.extend(["", "## Still Open"])
    lines.extend(f"- `{item}`" for item in payload["still_open"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
