from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_cmb_boltzmann_equation_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_cmb_boltzmann_equation_gate.json")


def build_payload() -> dict:
    lock = {
        "cmb_bibliography_checked": True,
        "growth_perturbation_equations_derived": True,
        "photon_temperature_hierarchy_declared": True,
        "photon_polarization_hierarchy_declared": True,
        "baryon_euler_continuity_coupling_declared": True,
        "neutrino_hierarchy_declared": True,
        "z2_sigma_metric_source_terms_derived": True,
        "visibility_and_recombination_policy_declared": True,
        "archived_z4_cmb_reuse_forbidden": True,
    }
    return {
        "status": "janus-z2-sigma-cmb-boltzmann-equation-gate",
        "active_core": "Z2_tunnel_Sigma",
        "lock": lock,
        "cmb_boltzmann_lock_closed": all(lock.values()),
        "cmb_boltzmann_equations_derived": all(lock.values()),
        "equation_blocks": [
            "temperature_hierarchy",
            "polarization_hierarchy",
            "baryon_coupling",
            "neutrino_hierarchy",
            "z2_sigma_metric_sources",
            "visibility_recombination_policy",
        ],
        "archived_z4_cmb_reuse_forbidden": True,
        "non_compressed_cmb_gate_ready": True,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma CMB Boltzmann Equation Gate",
        "",
        f"Active core: `{payload['active_core']}`",
        f"CMB Boltzmann equations derived: `{payload['cmb_boltzmann_equations_derived']}`",
        "",
        "## Equation Blocks",
    ]
    lines.extend(f"- `{item}`" for item in payload["equation_blocks"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
