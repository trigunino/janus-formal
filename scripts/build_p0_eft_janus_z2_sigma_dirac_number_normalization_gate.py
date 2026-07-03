from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_dirac_number_normalization_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_dirac_number_normalization_gate.json")


def build_payload() -> dict:
    declared = {
        "Noether_charge_bibliography_checked": True,
        "Dirac_current_charge_integral_declared": True,
        "plus_sector_charge_declared": True,
        "minus_sector_charge_declared": True,
        "Z2Sigma_projection_charge_declared": True,
        "anomaly_or_boundary_leak_guard_declared": True,
        "observational_fit_forbidden": True,
    }
    closure = {
        "plus_charge_fixed_by_action_or_topology": False,
        "minus_charge_fixed_by_action_or_topology": False,
        "projected_charge_fixed_by_Z2Sigma": False,
        "number_normalizations_ready": False,
    }
    return {
        "status": "janus-z2-sigma-dirac-number-normalization-gate",
        "active_core": "Z2_tunnel_Sigma",
        "primary_sources_checked": [
            "Dirac U(1) Noether charge literature",
            "conserved-current charge integrals on curved hypersurfaces",
            "active Z2/Sigma projected throat ledger",
        ],
        "bibliography_result": (
            "Generic sources give the conserved charge integral of a covariantly "
            "conserved Dirac current. They do not fix the active Janus Z2/Sigma "
            "charges N_plus, N_minus, or the projected throat normalization."
        ),
        "declared": declared,
        "closure": closure,
        "formulas": {
            "plus_charge": "N_+ = integral_{Sigma_t^+} J_+^mu dSigma_mu",
            "minus_charge": "N_- = integral_{Sigma_t^-} J_-^mu dSigma_mu",
            "projected_charge": "N_Z2Sigma = P_Z2Sigma(N_+, N_-)",
            "density_law": "n_pm(a) = N_pm / a^3 once N_pm is fixed",
        },
        "dirac_number_normalization_ledger_declared": all(declared.values()),
        "dirac_number_normalization_ready": all(declared.values()) and all(closure.values()),
        "next_required": [
            "derive_N_plus_from_active_spinor_boundary_data",
            "derive_N_minus_from_active_spinor_boundary_data",
            "derive_Z2Sigma_projected_number_charge",
            "propagate_number_normalization_to_density_gate",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Dirac Number Normalization Gate",
        "",
        f"Active core: `{payload['active_core']}`",
        f"Ledger declared: `{payload['dirac_number_normalization_ledger_declared']}`",
        f"Number normalization ready: `{payload['dirac_number_normalization_ready']}`",
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
