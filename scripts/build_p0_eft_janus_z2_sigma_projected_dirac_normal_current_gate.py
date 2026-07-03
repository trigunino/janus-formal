from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_projected_dirac_normal_current_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_projected_dirac_normal_current_gate.json")


def build_payload() -> dict:
    declared = {
        "thin_shell_flux_bibliography_checked": True,
        "projected_Dirac_matter_current_gate_declared": True,
        "tangent_normal_orientation_gate_declared": True,
        "plus_normal_current_declared": True,
        "minus_normal_current_declared": True,
        "Z2_projected_normal_current_declared": True,
        "no_fit_transparency_decision": True,
        "observational_fit_forbidden": True,
    }
    closure = {
        "projected_Dirac_matter_current_ready": False,
        "Sigma_normals_ready": False,
        "plus_normal_current_ready": False,
        "minus_normal_current_ready": False,
        "Z2_projected_normal_current_ready": False,
        "no_normal_matter_current_derived": False,
    }
    return {
        "status": "janus-z2-sigma-projected-dirac-normal-current-gate",
        "active_core": "Z2_tunnel_Sigma",
        "primary_sources_checked": [
            "thin-shell conservation identity with normal momentum flux",
            "Dirac U(1) Noether current normal projection",
            "active projected Dirac matter-current and tangent/normal gates",
        ],
        "bibliography_result": (
            "Thin-shell literature supplies the normal-flux slot and Dirac theory "
            "supplies the current. The active Z2/Sigma cancellation or leakage "
            "must still be derived from the projected current and Sigma normals."
        ),
        "source_links": [
            "https://link.aps.org/doi/10.1103/PhysRevD.101.124035",
            "https://cosmo.fis.fc.ul.pt/~crawford/papers/cqg204034p17.pdf",
            "https://en.wikipedia.org/wiki/Dirac_equation",
        ],
        "declared": declared,
        "closure": closure,
        "formulas": {
            "plus_normal_current": "J_n^+ = J_+^mu n_mu^+",
            "minus_normal_current": "J_n^- = J_-^mu n_mu^-",
            "z2_projected_normal_current": "J_n^Z2Sigma = J_n^+ + eps_Z2 J_n^-",
            "transparency_test": "transparent Dirac branch requires J_n^Z2Sigma = 0",
        },
        "projected_dirac_normal_current_ledger_declared": all(declared.values()),
        "projected_dirac_normal_current_ready": all(declared.values())
        and all(value for key, value in closure.items() if key != "no_normal_matter_current_derived"),
        "no_normal_dirac_current_ready": all(declared.values()) and all(closure.values()),
        "next_required": [
            "pass_projected_Dirac_matter_current_gate",
            "pass_tangent_normal_orientation_gate",
            "project_J_plus_and_J_minus_on_Sigma_normals",
            "derive_or_reject_J_n_Z2Sigma_equals_zero",
            "feed_result_to_matter_flux_transparency_gate",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Projected Dirac Normal Current Gate",
        "",
        f"Active core: `{payload['active_core']}`",
        f"Ledger declared: `{payload['projected_dirac_normal_current_ledger_declared']}`",
        f"Normal current ready: `{payload['projected_dirac_normal_current_ready']}`",
        f"No-normal-current ready: `{payload['no_normal_dirac_current_ready']}`",
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
