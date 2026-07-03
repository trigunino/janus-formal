from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_bulk_stress_normal_flux_cancellation_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_bulk_stress_normal_flux_cancellation_gate.json")


def build_payload() -> dict:
    declared = {
        "thin_shell_momentum_flux_bibliography_checked": True,
        "bulk_stress_of_a_gate_declared": True,
        "tangent_normal_orientation_gate_declared": True,
        "plus_flux_projection_declared": True,
        "minus_flux_projection_declared": True,
        "Z2_flux_cancellation_declared": True,
        "no_fit_transparency_decision": True,
        "observational_fit_forbidden": True,
    }
    closure = {
        "bulk_stress_plus_of_a_ready": False,
        "bulk_stress_minus_of_a_ready": False,
        "Sigma_tangents_ready": False,
        "Sigma_normals_ready": False,
        "plus_flux_projection_ready": False,
        "minus_flux_projection_ready": False,
        "Z2_flux_cancellation_derived": False,
        "bulk_stress_normal_projection_zero_derived": False,
    }
    projection_keys = [
        "bulk_stress_plus_of_a_ready",
        "bulk_stress_minus_of_a_ready",
        "Sigma_tangents_ready",
        "Sigma_normals_ready",
        "plus_flux_projection_ready",
        "minus_flux_projection_ready",
    ]
    return {
        "status": "janus-z2-sigma-bulk-stress-normal-flux-cancellation-gate",
        "active_core": "Z2_tunnel_Sigma",
        "primary_sources_checked": [
            "Israel thin-shell conservation identity",
            "Poisson-Visser transparent/non-transparent thin-shell branches",
            "dynamic thin-shell momentum-flux term T_munu e_a^mu n^nu",
        ],
        "bibliography_result": (
            "Generic thin-shell machinery supplies the normal bulk-stress flux. "
            "It does not decide whether active Janus/Sigma has zero flux or an "
            "exact Z2 cancellation."
        ),
        "source_links": [
            "https://doi.org/10.1007/BF02710419",
            "https://arxiv.org/abs/gr-qc/9506083",
            "https://arxiv.org/pdf/gr-qc/9506083",
            "https://cosmo.fis.fc.ul.pt/~crawford/papers/cqg204034p17.pdf",
        ],
        "declared": declared,
        "closure": closure,
        "formulas": {
            "plus_flux": "F_a^+ = T^+_munu e_a^mu n_+^nu",
            "minus_flux": "F_a^- = T^-_munu e_a^mu n_-^nu",
            "z2_net_flux": "F_a^Z2Sigma = F_a^+ + eps_Z2 F_a^-",
            "cancellation_test": "F_a^Z2Sigma = 0",
        },
        "bulk_stress_normal_flux_cancellation_ledger_declared": all(declared.values()),
        "bulk_stress_normal_flux_projection_ready": all(declared.values())
        and all(closure[key] for key in projection_keys),
        "bulk_stress_normal_flux_cancellation_ready": all(declared.values()) and all(closure.values()),
        "next_required": [
            "pass_bulk_stress_of_a_gate",
            "pass_tangent_normal_orientation_gate",
            "derive_F_plus_and_F_minus",
            "prove_or_reject_Z2_flux_cancellation",
            "feed_result_to_matter_flux_transparency_gate",
            "if_cancellation_fails_feed_active_flux_projection_gate",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Bulk-Stress Normal-Flux Cancellation Gate",
        "",
        f"Active core: `{payload['active_core']}`",
        f"Ledger declared: `{payload['bulk_stress_normal_flux_cancellation_ledger_declared']}`",
        f"Projection ready: `{payload['bulk_stress_normal_flux_projection_ready']}`",
        f"Cancellation ready: `{payload['bulk_stress_normal_flux_cancellation_ready']}`",
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
