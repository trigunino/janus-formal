from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_mirror_recombination_roadmap.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_mirror_recombination_roadmap.json")


def build_payload() -> dict:
    state_vector = [
        "delta_gamma_plus",
        "theta_gamma_plus",
        "delta_b_plus",
        "theta_b_plus",
        "Phi_plus",
        "Psi_plus",
        "delta_gamma_minus",
        "theta_gamma_minus",
        "delta_b_minus",
        "theta_b_minus",
        "Phi_minus",
        "Psi_minus",
        "delta_chi_torsion",
        "delta_chi_torsion_prime",
    ]
    equations = [
        "two_sector_photon_baryon_hierarchy",
        "separate_visibility_histories_g_plus_g_minus",
        "mirror_temperature_ratio_T_minus_equals_xi_T_plus",
        "Z4_projection_only_at_observable_source_level",
        "line_of_sight_kernel_Delta_l_plus_with_G_l_Z4",
        "no_early_rho_plus_minus_collapse",
    ]
    blockers = [
        "derive coupled recombination visibility g_plus/g_minus",
        "derive TT acoustic phase source with hidden-sector imprint",
        "derive Weyl/lensing projection from Z4 geodesic transport",
    ]
    return {
        "status": "janus-z4-mirror-recombination-roadmap",
        "solver_numerics_modified": False,
        "planck_validation_claimed": False,
        "roadmap_only": True,
        "state_vector": state_vector,
        "required_equations": equations,
        "anti_shortcuts": {
            "collapse_to_rho_eff_before_projection_allowed": False,
            "fit_visibility_or_phase_by_observation_allowed": False,
            "use_camb_class_as_container_allowed": False,
            "use_camb_class_as_reference_blocks_allowed": True,
        },
        "blockers": blockers,
        "ready_to_implement_next_block": True,
        "next_block": (
            "Implement coupled visibility/recombination and TT phase transport using the explicit "
            "plus/minus state vector, then run the observable oscilloscope before any Planck gate."
        ),
    }


def write_reports() -> dict:
    payload = build_payload()
    JSON_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2, sort_keys=True), encoding="utf-8")
    lines = [
        "# Janus Z4 Mirror/Recombination Roadmap",
        "",
        f"Status: `{payload['status']}`",
        f"Roadmap only: `{payload['roadmap_only']}`",
        f"Planck validation claimed: `{payload['planck_validation_claimed']}`",
        "",
        "## State Vector",
    ]
    lines.extend(f"- `{item}`" for item in payload["state_vector"])
    lines.extend(["", "## Required Equations"])
    lines.extend(f"- `{item}`" for item in payload["required_equations"])
    lines.extend(["", "## Anti-Shortcuts"])
    for key, value in payload["anti_shortcuts"].items():
        lines.append(f"- `{key}`: `{value}`")
    lines.extend(["", "## Blockers"])
    lines.extend(f"- {item}" for item in payload["blockers"])
    lines.extend(["", "## Next", payload["next_block"]])
    REPORT_PATH.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return payload


if __name__ == "__main__":
    write_reports()
