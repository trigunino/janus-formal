from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_matter_flux_active_projection_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_matter_flux_active_projection_gate.json")


def build_payload() -> dict:
    declared = {
        "thin_shell_flux_projection_bibliography_checked": True,
        "transparency_not_assumed": True,
        "plus_bulk_stress_declared": True,
        "minus_bulk_stress_declared": True,
        "bulk_stress_normal_flux_cancellation_gate_declared": True,
        "bulk_stress_of_a_gate_declared": True,
        "Sigma_tangents_declared": True,
        "Sigma_normals_declared": True,
        "Z2_orientation_projection_declared": True,
        "observational_fit_forbidden": True,
        "F_plus_projection_declared": True,
        "F_minus_projection_declared": True,
        "net_flux_projection_declared": True,
    }
    closure = {
        "plus_bulk_stress_of_a_ready": False,
        "minus_bulk_stress_of_a_ready": False,
        "embedding_of_a_ready": False,
        "active_flux_of_a_ready": False,
    }
    return {
        "status": "janus-z2-sigma-matter-flux-active-projection-gate",
        "active_core": "Z2_tunnel_Sigma",
        "primary_sources_checked": [
            "Israel thin-shell surface conservation identity",
            "Poisson-Visser momentum-flux treatment",
            "Singular hypersurfaces and thin shells in cosmology, arXiv:2402.09539",
            "active bulk-stress normal-flux cancellation gate",
        ],
        "bibliography_result": (
            "The active non-transparent branch is computed by projecting each bulk stress "
            "tensor on Sigma tangents and normals. No source supplies the active Janus "
            "bulk stresses or embedding functions of scale factor."
        ),
        "declared": declared,
        "closure": closure,
        "formula": {
            "plus_flux": "F_a^+ = T_munu^+ e_a^mu n_+^nu",
            "minus_flux": "F_a^- = T_munu^- e_a^mu n_-^nu",
            "net_flux": "F_a^Z2Sigma = F_a^+ + eps_Z2 F_a^-",
        },
        "active_flux_projection_ledger_declared": all(declared.values()),
        "active_flux_projection_ready": all(declared.values()) and all(closure.values()),
        "next_required": [
            "pass_bulk_stress_of_a_gate",
            "pass_bulk_stress_normal_flux_cancellation_gate_or_record_nonzero_flux",
            "derive_active_embedding_tangents_and_normals_of_a",
            "evaluate_F_a_Z2Sigma_of_a",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Matter-Flux Active Projection Gate",
        "",
        f"Active core: `{payload['active_core']}`",
        f"Ledger declared: `{payload['active_flux_projection_ledger_declared']}`",
        f"Projection ready: `{payload['active_flux_projection_ready']}`",
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
