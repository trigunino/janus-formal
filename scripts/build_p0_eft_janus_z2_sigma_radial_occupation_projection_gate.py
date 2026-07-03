from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_radial_occupation_projection_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_radial_occupation_projection_gate.json")


def build_payload() -> dict:
    declared = {
        "equivariant_projection_bibliography_checked": True,
        "Fermi_Dirac_isotropy_gate_declared": True,
        "Z2Sigma_projection_map_declared": True,
        "rotation_equivariance_criterion_declared": True,
        "plus_radial_occupation_declared": True,
        "minus_radial_occupation_declared": True,
        "projected_radial_occupation_declared": True,
        "observational_fit_forbidden": True,
    }
    closure = {
        "plus_radial_occupation_ready": False,
        "minus_radial_occupation_ready": False,
        "Z2Sigma_projection_map_derived": False,
        "projection_rotation_equivariant_derived": False,
        "projected_radial_occupation_derived": False,
        "radial_occupation_projection_ready": False,
    }
    return {
        "status": "janus-z2-sigma-radial-occupation-projection-gate",
        "active_core": "Z2_tunnel_Sigma",
        "primary_sources_checked": [
            "standard equivariant-map/invariant-function machinery",
            "Janus Z2/Sigma Dirac Fermi-Dirac isotropy gate",
            "active Sigma spinor/projection map gates",
        ],
        "source_links": [
            "https://en.wikipedia.org/wiki/Equivariant_map",
            "https://www.sci.unich.it/geodeep2022/slides/Groups_Representations_and_Equivariance.pdf",
        ],
        "bibliography_result": (
            "Equivariance supplies the generic rule: if the projection commutes with "
            "the rotation action, radial/invariant occupations remain radial. The active "
            "Janus Z2/Sigma model still has to derive this rotation-equivariance for its "
            "projection map."
        ),
        "declared": declared,
        "closure": closure,
        "formulas": {
            "radial_inputs": "f_+(q_vec,a)=f_+(|q|,a), f_-(q_vec,a)=f_-(|q|,a)",
            "equivariance": "P_Z2Sigma(R q)=R P_Z2Sigma(q) for FLRW momentum rotations R",
            "projection": "f_Z2Sigma(q,a)=P_Z2Sigma(f_+(q,a),f_-(q,a))",
            "radial_output": "f_Z2Sigma(q_vec,a)=f_Z2Sigma(|q|,a)",
        },
        "radial_occupation_projection_ledger_declared": all(declared.values()),
        "radial_occupation_projection_ready": all(declared.values()) and all(closure.values()),
        "next_required": [
            "pass_Dirac_Fermi_Dirac_isotropy_gate",
            "derive_Z2Sigma_projection_map",
            "prove_projection_rotation_equivariance",
            "feed_result_to_distribution_isotropy_anisotropic_stress_gate",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Radial Occupation Projection Gate",
        "",
        f"Active core: `{payload['active_core']}`",
        f"Ledger declared: `{payload['radial_occupation_projection_ledger_declared']}`",
        f"Projection ready: `{payload['radial_occupation_projection_ready']}`",
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
