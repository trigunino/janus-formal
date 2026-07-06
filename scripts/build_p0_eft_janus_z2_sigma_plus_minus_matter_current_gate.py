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

REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_plus_minus_matter_current_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_plus_minus_matter_current_gate.json")


def build_payload() -> dict:
    matter_action = build_dirac_matter_action_payload()
    plus_action_ready = matter_action["closure"]["plus_matter_action_ready"]
    minus_action_ready = matter_action["closure"]["minus_matter_action_ready"]
    currents_ready = plus_action_ready and minus_action_ready
    declared = {
        "Dirac_Noether_current_bibliography_checked": True,
        "plus_minus_Dirac_matter_action_gate_declared": True,
        "projected_Dirac_matter_current_gate_declared": True,
        "plus_minus_matter_actions_declared": True,
        "Dirac_current_formula_imported": True,
        "plus_current_declared": True,
        "minus_current_declared": True,
        "covariant_conservation_guard_declared": True,
        "observational_fit_forbidden": True,
    }
    closure = {
        "plus_matter_action_ready": plus_action_ready,
        "minus_matter_action_ready": minus_action_ready,
        "plus_current_ready": currents_ready,
        "minus_current_ready": currents_ready,
        "plus_minus_matter_currents_ready": currents_ready,
    }
    return {
        "status": "janus-z2-sigma-plus-minus-matter-current-gate",
        "active_core": "Z2_tunnel_Sigma",
        "primary_sources_checked": [
            "Dirac global U(1) Noether current",
            "Dirac equation in curved spacetime/tetrad formalism",
            "active Dirac fermion number-density gate",
            "active plus/minus Dirac matter-action gate",
            "active projected Dirac matter-current gate",
        ],
        "bibliography_result": (
            "Generic Dirac theory supplies J^mu = psi_bar gamma^mu psi and "
            "covariant conservation under the usual source/anomaly guards. It does "
            "not supply the active Janus plus/minus matter actions."
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
            "plus_current": "J_+^mu = psi_bar_+ gamma_+^mu psi_+",
            "minus_current": "J_-^mu = psi_bar_- gamma_-^mu psi_-",
            "conservation_guard": "nabla_mu J_pm^mu = 0 unless active boundary leakage/anomaly is derived",
        },
        "plus_minus_matter_current_ledger_declared": all(declared.values()),
        "plus_minus_matter_current_ready": all(declared.values()) and all(closure.values()),
        "gate_passed": all(declared.values()) and all(closure.values()),
        "primary_blocker": "none" if all(closure.values()) else "plus_minus_Dirac_matter_action",
        "next_required": [
            "keep_normal_flux_and_density_laws_separate_from_Noether_current",
            "feed_plus_minus_currents_to_normal_matter_current_gate",
            "feed_number_currents_to_Dirac_number_density_gate",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Plus/Minus Matter Current Gate",
        "",
        f"Active core: `{payload['active_core']}`",
        f"Ledger declared: `{payload['plus_minus_matter_current_ledger_declared']}`",
        f"Currents ready: `{payload['plus_minus_matter_current_ready']}`",
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
