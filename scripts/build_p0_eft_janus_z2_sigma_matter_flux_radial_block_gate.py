from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_matter_flux_radial_block_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_matter_flux_radial_block_gate.json")


def build_payload() -> dict:
    declared = {
        "thin_shell_flux_bibliography_checked": True,
        "normal_tangent_flux_formula_ready": True,
        "radial_flux_variation_declared": True,
        "transparency_branch_declared": True,
        "matter_flux_route_decision_gate_declared": True,
        "transparency_gate_declared": True,
        "active_flux_projection_gate_declared": True,
        "active_bulk_stress_projection_required": True,
        "Z2_flux_orientation_declared": True,
        "observational_fit_forbidden": True,
        "E_matterFlux_block_declared": True,
    }
    closure = {
        "transparency_condition_derived": False,
        "active_flux_of_a_ready": False,
        "E_matterFlux_radial_block_reduced": False,
    }
    return {
        "status": "janus-z2-sigma-matter-flux-radial-block-gate",
        "active_core": "Z2_tunnel_Sigma",
        "primary_sources_checked": [
            "Israel thin-shell surface conservation identity",
            "Poisson-Visser thin-shell wormhole momentum-flux conservation",
            "Dynamic thin-shell wormhole flux terms in surface Bianchi identities",
            "active matter-flux route decision gate",
        ],
        "bibliography_result": (
            "Thin-shell literature supplies the normal-tangent flux term and the "
            "transparent-shell branch. It does not decide whether the active Janus "
            "tunnel throat is transparent or carries a nonzero projected matter flux."
        ),
        "declared": declared,
        "closure": closure,
        "formula": {
            "flux_one_form": "F_a^pm = T_munu^pm e_a^mu n_pm^nu",
            "radial_block": "E_matterFlux = delta_RSigma integral_Sigma F_tau^Z2Sigma or 0 under derived transparency",
            "transparency_branch": "E_matterFlux = 0 only if F_a^Z2Sigma = 0 is derived from active Sigma physics",
        },
        "matter_flux_radial_ledger_declared": all(declared.values()),
        "matter_flux_radial_block_reduced": all(declared.values())
        and (closure["transparency_condition_derived"] or closure["active_flux_of_a_ready"])
        and closure["E_matterFlux_radial_block_reduced"],
        "next_required": [
            "pass_matter_flux_transparency_gate_or_reject_transparency",
            "pass_matter_flux_route_decision_gate",
            "pass_matter_flux_active_projection_gate_if_not_transparent",
            "evaluate_F_a_Z2Sigma_of_a",
            "reduce_E_matterFlux_radial_block",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Matter-Flux Radial Block Gate",
        "",
        f"Active core: `{payload['active_core']}`",
        f"Ledger declared: `{payload['matter_flux_radial_ledger_declared']}`",
        f"Block reduced: `{payload['matter_flux_radial_block_reduced']}`",
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
