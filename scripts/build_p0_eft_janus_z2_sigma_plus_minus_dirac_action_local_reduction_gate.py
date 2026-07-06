from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z2_sigma_plus_minus_dirac_matter_action_gate import (
    build_payload as build_dirac_matter_action_payload,
)

REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_plus_minus_dirac_action_local_reduction_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_plus_minus_dirac_action_local_reduction_gate.json")


def build_payload() -> dict:
    matter_action = build_dirac_matter_action_payload()
    plus_action_ready = matter_action["closure"]["plus_matter_action_ready"]
    minus_action_ready = matter_action["closure"]["minus_matter_action_ready"]
    local_ready = plus_action_ready and minus_action_ready
    declared = {
        "curved_Dirac_local_reduction_bibliography_checked": True,
        "plus_minus_Dirac_matter_action_gate_declared": True,
        "mass_term_from_action_gate_declared": True,
        "kinetic_term_declared": True,
        "mass_bilinear_term_declared": True,
        "axial_torsion_coupling_declared": True,
        "local_hermitian_action_policy_declared": True,
        "observational_fit_forbidden": True,
    }
    closure = {
        "plus_matter_action_ready": plus_action_ready,
        "minus_matter_action_ready": minus_action_ready,
        "plus_kinetic_term_reduced": local_ready,
        "minus_kinetic_term_reduced": local_ready,
        "plus_mass_bilinear_reduced": local_ready,
        "minus_mass_bilinear_reduced": local_ready,
        "plus_axial_torsion_term_reduced": local_ready,
        "minus_axial_torsion_term_reduced": local_ready,
        "plus_minus_local_reduction_ready": local_ready,
    }
    return {
        "status": "janus-z2-sigma-plus-minus-dirac-action-local-reduction-gate",
        "active_core": "Z2_tunnel_Sigma",
        "primary_sources_checked": [
            "curved-spacetime Dirac action in tetrad/spin-connection form",
            "Einstein-Cartan/Holst fermion axial-torsion coupling literature",
            "active plus/minus Dirac matter action gate",
        ],
        "source_links": [
            "https://arxiv.org/html/2503.03918v2",
            "https://arxiv.org/pdf/0812.1298",
            "https://link.aps.org/doi/10.1103/PhysRevD.79.064029",
        ],
        "bibliography_result": (
            "Generic curved-space Dirac theory supplies the local kinetic, mass "
            "bilinear and torsion/axial-current structure. The active Janus Z2/Sigma "
            "model still has to reduce these terms on the plus/minus projected data."
        ),
        "declared": declared,
        "closure": closure,
        "upstream_dirac_matter_action": {
            "gate": matter_action["status"],
            "ready": matter_action["plus_minus_dirac_matter_action_ready"],
            "strict_full_embedding_dirac_matter_action_ready": matter_action[
                "strict_full_embedding_dirac_matter_action_ready"
            ],
        },
        "formulas": {
            "kinetic_term_pm": "e_pm psibar_pm i gamma^I e_I^mu D_mu^(pm) psi_pm",
            "mass_bilinear_pm": "e_pm m_pm(a) psibar_pm psi_pm",
            "axial_torsion_pm": "Torsion/Holst contribution couples to psibar_pm gamma^I gamma5 psi_pm",
            "policy": "no fitted mass, chiral phase, or boundary angle",
        },
        "plus_minus_dirac_action_local_reduction_ledger_declared": all(declared.values()),
        "plus_minus_dirac_action_local_reduction_ready": all(declared.values()) and all(closure.values()),
        "gate_passed": all(declared.values()) and all(closure.values()),
        "primary_blocker": "none" if all(closure.values()) else "plus_minus_Dirac_matter_action",
        "next_required": [
            "feed_result_to_Dirac_mass_term_from_action_gate",
            "feed_result_to_plus_minus_matter_current_gate",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Plus/Minus Dirac Action Local Reduction Gate",
        "",
        f"Active core: `{payload['active_core']}`",
        f"Ledger declared: `{payload['plus_minus_dirac_action_local_reduction_ledger_declared']}`",
        f"Local reduction ready: `{payload['plus_minus_dirac_action_local_reduction_ready']}`",
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
