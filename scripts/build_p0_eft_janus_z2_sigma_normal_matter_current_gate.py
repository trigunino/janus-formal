from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_normal_matter_current_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_normal_matter_current_gate.json")


def build_payload() -> dict:
    declared = {
        "matter_current_bibliography_checked": True,
        "Noether_current_formula_imported": True,
        "plus_minus_matter_current_gate_declared": True,
        "projected_Dirac_matter_current_gate_declared": True,
        "projected_Dirac_normal_current_gate_declared": True,
        "normal_projection_criterion_declared": True,
        "Sigma_normals_required": True,
        "Z2_projected_current_declared": True,
        "observational_fit_forbidden": True,
    }
    closure = {
        "plus_matter_current_ready": False,
        "minus_matter_current_ready": False,
        "Sigma_normals_ready": False,
        "Z2_projected_normal_current_ready": False,
        "no_normal_matter_current_derived": False,
    }
    return {
        "status": "janus-z2-sigma-normal-matter-current-gate",
        "active_core": "Z2_tunnel_Sigma",
        "primary_sources_checked": [
            "stress-energy/matter current normal-flux definitions",
            "thin-shell transparency no-normal-flux condition",
            "Dirac U(1) Noether current references for fermionic matter",
            "active plus/minus matter-current gate",
            "active projected Dirac matter-current gate",
            "active projected Dirac normal-current gate",
        ],
        "bibliography_result": (
            "Generic current conservation supplies a matter current and its normal "
            "projection. It does not supply the active Janus plus/minus current or "
            "the active Sigma normals."
        ),
        "declared": declared,
        "closure": closure,
        "formula": {
            "normal_current_plus": "J_n^+ = J_mu^+ n_+^mu",
            "normal_current_minus": "J_n^- = J_mu^- n_-^mu",
            "z2_projected_normal_current": "J_n^Z2Sigma = J_n^+ + eps_Z2 J_n^-",
            "no_normal_current": "J_n^Z2Sigma = 0",
        },
        "normal_matter_current_ledger_declared": all(declared.values()),
        "no_normal_matter_current_ready": all(declared.values()) and all(closure.values()),
        "next_required": [
            "derive_plus_minus_matter_currents_from_active_matter_action",
            "pass_plus_minus_matter_current_gate",
            "pass_projected_Dirac_matter_current_gate",
            "pass_projected_Dirac_normal_current_gate",
            "pass_tangent_normal_orientation_gate",
            "project_currents_on_Sigma_normals",
            "prove_or_reject_J_n_Z2Sigma_equals_zero",
            "feed_result_to_matter_flux_transparency_gate",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Normal Matter Current Gate",
        "",
        f"Active core: `{payload['active_core']}`",
        f"Ledger declared: `{payload['normal_matter_current_ledger_declared']}`",
        f"No-normal-current ready: `{payload['no_normal_matter_current_ready']}`",
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
