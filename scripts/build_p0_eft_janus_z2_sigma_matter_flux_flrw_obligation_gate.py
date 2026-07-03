from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_matter_flux_flrw_obligation_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_matter_flux_flrw_obligation_gate.json")


def build_payload() -> dict:
    method = {
        "thin_shell_flux_bibliography_checked": True,
        "Sigma_embedding_data_available": True,
        "bulk_stress_tensors_declared": True,
        "normal_tangent_flux_formula_ready": True,
        "transparency_condition_declared": True,
        "Z2_flux_orientation_declared": True,
        "visible_matter_flux_component_declared": True,
    }
    closure = {
        "FLRW_matter_flux_reduced": False,
        "matter_flux_rho_p_of_a_ready": False,
    }
    return {
        "status": "janus-z2-sigma-matter-flux-flrw-obligation-gate",
        "active_core": "Z2_tunnel_Sigma",
        "primary_sources_checked": [
            "Thin-shell surface conservation / Codazzi flux identity",
            "Singular hypersurfaces and thin shells in cosmology, arXiv:2402.09539",
            "Einstein-Cartan junction literature for torsion-bearing shells",
        ],
        "bibliography_result": (
            "Generic shell flux uses T_munu e_a^mu n^nu and transparency conditions. "
            "No active Janus Z2/Sigma matter-flux function of a was found."
        ),
        "method": method,
        "closure": closure,
        "formulas": {
            "flux_one_form": "F_a^pm = T_munu^pm e_a^mu n_pm^nu",
            "net_flux": "F_a^Z2Sigma = F_a^+ + eps_Z2 F_a^- after orientation projection",
            "transparency": "F_a^Z2Sigma = 0 when no matter crosses Sigma",
        },
        "matter_flux_method_ready": all(method.values()),
        "matter_flux_FLRW_closure_ready": all(method.values()) and all(closure.values()),
        "next_required": [
            "derive_bulk_T_munu_plus_minus_on_active_Z2Sigma_background",
            "project_T_munu_e_a_n_to_FLRW_flux_components",
            "decide_or_derive_transparency_condition_for_tunnel_throat",
            "reduce_matter_flux_to_rho_p_of_a_or_zero",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Matter Flux FLRW Obligation Gate",
        "",
        f"Active core: `{payload['active_core']}`",
        f"Method ready: `{payload['matter_flux_method_ready']}`",
        f"FLRW closure ready: `{payload['matter_flux_FLRW_closure_ready']}`",
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
