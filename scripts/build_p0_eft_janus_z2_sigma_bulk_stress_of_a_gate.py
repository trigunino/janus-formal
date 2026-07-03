from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_bulk_stress_of_a_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_bulk_stress_of_a_gate.json")


def build_payload() -> dict:
    declared = {
        "Janus_bimetric_stress_bibliography_checked": True,
        "plus_sector_stress_declared": True,
        "minus_sector_stress_declared": True,
        "sector_density_pressure_gate_declared": True,
        "Holst_torsion_stress_gate_declared": True,
        "perfect_fluid_FLRW_stress_imported": True,
        "Holst_torsion_stress_contribution_declared": True,
        "Z2_sign_policy_declared": True,
        "observational_fit_forbidden": True,
        "T_plus_munu_of_a_declared": True,
        "T_minus_munu_of_a_declared": True,
    }
    closure = {
        "plus_matter_density_pressure_of_a_ready": False,
        "minus_matter_density_pressure_of_a_ready": False,
        "torsion_stress_of_a_ready": False,
        "bulk_stress_plus_of_a_ready": False,
        "bulk_stress_minus_of_a_ready": False,
    }
    return {
        "status": "janus-z2-sigma-bulk-stress-of-a-gate",
        "active_core": "Z2_tunnel_Sigma",
        "primary_sources_checked": [
            "Petit/Margnat/Zejli 2024, arXiv:2412.04644",
            "Janus bimetric coupled field-equation literature",
            "standard FLRW perfect-fluid stress tensor",
            "Holst/Nieh-Yan torsion stress literature",
        ],
        "bibliography_result": (
            "Janus/bimetric sources motivate plus/minus sector stress tensors and "
            "standard FLRW supplies perfect-fluid form. No source supplies active "
            "Z2/Sigma T_plus/minus(a) including Holst torsion on the resolved throat."
        ),
        "declared": declared,
        "closure": closure,
        "formula": {
            "perfect_fluid": "T_munu^(pm) = (rho_pm+p_pm) u_mu u_nu + p_pm g_munu^(pm)",
            "active_bulk": "T_munu^(pm,active)(a) = T_matter^(pm)(a) + T_HolstTorsion^(pm)(a)",
            "sign_policy": "gravitational Z2 sign is not thermodynamic negative density unless derived",
        },
        "bulk_stress_ledger_declared": all(declared.values()),
        "bulk_stress_of_a_ready": all(declared.values()) and all(closure.values()),
        "next_required": [
            "pass_sector_density_pressure_of_a_gate",
            "pass_Holst_torsion_stress_of_a_gate",
            "assemble_T_plus_minus_munu_of_a",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Bulk Stress Of A Gate",
        "",
        f"Active core: `{payload['active_core']}`",
        f"Ledger declared: `{payload['bulk_stress_ledger_declared']}`",
        f"Bulk stress ready: `{payload['bulk_stress_of_a_ready']}`",
        "",
        "## Formula",
    ]
    lines.extend(f"- `{key}`: `{value}`" for key, value in payload["formula"].items())
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
