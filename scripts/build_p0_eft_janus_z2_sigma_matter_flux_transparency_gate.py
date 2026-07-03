from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_matter_flux_transparency_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_matter_flux_transparency_gate.json")


def build_payload() -> dict:
    criteria = {
        "thin_shell_transparency_bibliography_checked": True,
        "no_normal_matter_current_criterion_declared": True,
        "normal_matter_current_gate_declared": True,
        "bulk_stress_normal_projection_criterion_declared": True,
        "Sigma_as_geometric_throat_not_matter_portal_declared": True,
        "Z2_flux_cancellation_criterion_declared": True,
        "observational_fit_forbidden": True,
        "transparency_sufficient_conditions_declared": True,
    }
    closure = {
        "no_normal_matter_current_derived": False,
        "bulk_stress_normal_projection_zero_derived": False,
        "Z2_flux_cancellation_derived": False,
        "active_Sigma_transparency_derived": False,
    }
    return {
        "status": "janus-z2-sigma-matter-flux-transparency-gate",
        "active_core": "Z2_tunnel_Sigma",
        "primary_sources_checked": [
            "Poisson-Visser transparent thin-shell wormhole branch",
            "Thin-shell surface conservation identity with momentum flux term",
            "Dynamic thin-shell literature using no energy-momentum flux across shell",
            "active normal-matter-current gate",
        ],
        "bibliography_result": (
            "Transparency is a standard branch when no matter/radiation crosses the shell. "
            "For active Janus/Sigma it must be derived from vanishing normal matter current, "
            "zero normal bulk-stress projection, or exact Z2 flux cancellation."
        ),
        "criteria": criteria,
        "closure": closure,
        "sufficient_condition": (
            "F_a^Z2Sigma = T_munu^+ e_a^mu n_+^nu + eps_Z2 T_munu^- e_a^mu n_-^nu = 0"
        ),
        "transparency_criteria_declared": all(criteria.values()),
        "active_sigma_transparency_ready": all(criteria.values()) and all(closure.values()),
        "next_required": [
            "derive_no_normal_matter_current_at_Sigma",
            "pass_normal_matter_current_gate",
            "derive_bulk_stress_normal_projection_zero_or_Z2_cancellation",
            "if_transparency_fails_compute_active_flux_F_a_of_a",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Matter-Flux Transparency Gate",
        "",
        f"Active core: `{payload['active_core']}`",
        f"Criteria declared: `{payload['transparency_criteria_declared']}`",
        f"Transparency ready: `{payload['active_sigma_transparency_ready']}`",
        "",
        "## Sufficient Condition",
        f"`{payload['sufficient_condition']}`",
        "",
        "## Next Required",
    ]
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
