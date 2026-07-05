from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_dirac_regime_selection_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_dirac_regime_selection_gate.json")


def build_payload() -> dict:
    declared = {
        "regime_bibliography_checked": True,
        "mass_over_decoupling_temperature_criterion_declared": True,
        "Dirac_decoupling_condition_gate_declared": True,
        "relativistic_route_declared": True,
        "massive_route_declared": True,
        "semi_relativistic_route_declared": True,
        "no_regime_chosen_by_fit": True,
        "observational_fit_forbidden": True,
    }
    closure = {
        "plus_m_over_Tdec_derived": False,
        "minus_m_over_Tdec_derived": False,
        "plus_regime_selected": False,
        "minus_regime_selected": False,
        "projected_regime_selected": False,
        "Dirac_regime_selection_ready": False,
    }
    return {
        "status": "janus-z2-sigma-dirac-regime-selection-gate",
        "active_core": "Z2_tunnel_Sigma",
        "primary_sources_checked": [
            "Trautner 2017, arXiv:1612.07249",
            "thermal relic and massive-neutrino distribution literature",
            "Dirac decoupling-condition gate",
            "active Dirac mass/temperature law gate",
        ],
        "bibliography_result": (
            "Generic sources classify relativistic, massive, and semi-relativistic "
            "fermion regimes by mass relative to decoupling temperature. The active "
            "Janus Z2/Sigma model must derive m_pm/T_dec_pm before selecting a route."
        ),
        "declared": declared,
        "closure": closure,
        "criteria": {
            "relativistic": "m_pm / T_dec_pm << 1",
            "massive": "m_pm / T_dec_pm >> 1 or late-time nonrelativistic transport required",
            "semi_relativistic": "m_pm / T_dec_pm = O(1)",
            "policy": "do not select regime from observational convenience",
        },
        "dirac_regime_ledger_declared": all(declared.values()),
        "dirac_regime_selection_ready": all(declared.values()) and all(closure.values()),
        "gate_passed": all(declared.values()) and all(closure.values()),
        "primary_blocker": (
            "none"
            if all(declared.values()) and all(closure.values())
            else "mass_temperature_ratio_from_active_distribution"
        ),
        "next_required": [
            "derive_plus_Dirac_mass_or_massless_condition",
            "derive_minus_Dirac_mass_or_massless_condition",
            "pass_Dirac_decoupling_condition_gate",
            "select_projected_Z2Sigma_fermion_regime",
            "propagate_regime_to_mass_temperature_law_gate",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Dirac Regime Selection Gate",
        "",
        f"Active core: `{payload['active_core']}`",
        f"Ledger declared: `{payload['dirac_regime_ledger_declared']}`",
        f"Regime ready: `{payload['dirac_regime_selection_ready']}`",
        "",
        "## Criteria",
    ]
    lines.extend(f"- `{key}`: `{value}`" for key, value in payload["criteria"].items())
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
