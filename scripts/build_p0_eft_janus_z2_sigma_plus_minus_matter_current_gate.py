from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_plus_minus_matter_current_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_plus_minus_matter_current_gate.json")


def build_payload() -> dict:
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
        "plus_matter_action_ready": False,
        "minus_matter_action_ready": False,
        "plus_current_ready": False,
        "minus_current_ready": False,
        "plus_minus_matter_currents_ready": False,
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
        "formulas": {
            "plus_current": "J_+^mu = psi_bar_+ gamma_+^mu psi_+",
            "minus_current": "J_-^mu = psi_bar_- gamma_-^mu psi_-",
            "conservation_guard": "nabla_mu J_pm^mu = 0 unless active boundary leakage/anomaly is derived",
        },
        "plus_minus_matter_current_ledger_declared": all(declared.values()),
        "plus_minus_matter_current_ready": all(declared.values()) and all(closure.values()),
        "next_required": [
            "derive_plus_matter_action_from_active_Z2Sigma_matter_sector",
            "derive_minus_matter_action_from_active_Z2Sigma_matter_sector",
            "pass_plus_minus_Dirac_matter_action_gate",
            "pass_projected_Dirac_matter_current_gate",
            "derive_J_plus_and_J_minus_from_Noether_variation",
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
