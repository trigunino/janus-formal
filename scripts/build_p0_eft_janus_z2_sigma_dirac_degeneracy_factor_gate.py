from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_dirac_degeneracy_factor_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_dirac_degeneracy_factor_gate.json")


def build_payload() -> dict:
    declared = {
        "spin_degeneracy_bibliography_checked": True,
        "Dirac_internal_degrees_declared": True,
        "plus_minus_spinor_bundle_data_gate_declared": True,
        "spinor_bundle_projection_gate_declared": True,
        "fermion_route_selection_gate_declared": True,
        "plus_degeneracy_factor_declared": True,
        "minus_degeneracy_factor_declared": True,
        "Z2Sigma_projected_degeneracy_declared": True,
        "no_degeneracy_fit": True,
        "observational_fit_forbidden": True,
    }
    closure = {
        "plus_spinor_bundle_ready": False,
        "minus_spinor_bundle_ready": False,
        "Dirac_route_selected": False,
        "spinor_projection_ready": False,
        "plus_degeneracy_factor_derived": False,
        "minus_degeneracy_factor_derived": False,
        "projected_degeneracy_factor_ready": False,
    }
    return {
        "status": "janus-z2-sigma-dirac-degeneracy-factor-gate",
        "active_core": "Z2_tunnel_Sigma",
        "primary_sources_checked": [
            "Fermi-Dirac distribution degeneracy factor literature",
            "thermal relic internal degrees-of-freedom counting",
            "spinor-bundle and Dirac route gates for active Z2/Sigma",
        ],
        "bibliography_result": (
            "Generic sources supply spin/internal degeneracy counting. They do not "
            "fix active Janus Z2/Sigma plus/minus degeneracy factors after spinor "
            "bundle projection and boundary conditions."
        ),
        "source_links": [
            "https://arxiv.org/html/2504.04813v1",
            "https://www.mdpi.com/2075-4434/4/4/78",
            "https://arxiv.org/pdf/astro-ph/9506072",
        ],
        "declared": declared,
        "closure": closure,
        "formulas": {
            "generic_factor": "n_pm(a)=g_pm/(2 pi^2) integral dq q^2 f_pm(q,a)",
            "dirac_count_policy": "g_pm is determined by active Dirac spinor bundle and particle/antiparticle convention",
            "projection": "g_Z2Sigma = P_Z2Sigma(g_+, g_-; spinor projection data)",
            "no_fit": "g_pm and g_Z2Sigma are not observational nuisance parameters",
        },
        "dirac_degeneracy_factor_ledger_declared": all(declared.values()),
        "dirac_degeneracy_factor_ready": all(declared.values()) and all(closure.values()),
        "next_required": [
            "pass_plus_minus_spinor_bundle_data_gate",
            "pass_spinor_bundle_projection_gate",
            "pass_fermion_route_selection_gate",
            "derive_plus_minus_Dirac_degeneracy_factors",
            "project_degeneracy_through_Z2Sigma",
            "feed_result_to_Dirac_thermal_occupation_gate",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Dirac Degeneracy Factor Gate",
        "",
        f"Active core: `{payload['active_core']}`",
        f"Ledger declared: `{payload['dirac_degeneracy_factor_ledger_declared']}`",
        f"Degeneracy factor ready: `{payload['dirac_degeneracy_factor_ready']}`",
        "",
        "## Formulas",
    ]
    lines.extend(f"- `{key}`: `{value}`" for key, value in payload["formulas"].items())
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
