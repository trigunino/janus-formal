from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_matter_flux_transparency_readiness_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_matter_flux_transparency_readiness_gate.json")


def build_payload() -> dict:
    declared = {
        "transparency_gate_imported": True,
        "normal_matter_current_gate_imported": True,
        "bulk_stress_flux_cancellation_gate_imported": True,
        "tangent_normal_orientation_gate_imported": True,
        "active_embedding_readiness_gate_imported": True,
        "thin_shell_transparency_bibliography_checked": True,
        "transparency_criteria_declared": True,
    }
    readiness = {
        "active_embedding_ready": False,
        "Sigma_normals_ready": False,
        "no_normal_matter_current_ready": False,
        "bulk_stress_normal_flux_projection_ready": False,
        "Z2_bulk_stress_cancellation_ready": False,
        "active_Sigma_transparency_ready": False,
    }
    return {
        "status": "janus-z2-sigma-matter-flux-transparency-readiness-gate",
        "active_core": "Z2_tunnel_Sigma",
        "primary_sources_checked": [
            "Israel 1966 shell conservation and normal momentum flux",
            "Poisson-Visser 1995 transparent thin-shell branch",
            "Darmois-Israel hypersurface stress-balance literature",
        ],
        "source_links": [
            "https://doi.org/10.1007/BF02710419",
            "https://link.aps.org/doi/10.1103/PhysRevD.52.7318",
            "https://arxiv.org/abs/gr-qc/9506083",
        ],
        "bibliography_result": (
            "Primary thin-shell literature supports a transparent branch when normal "
            "matter/stress flux through the shell vanishes. For Janus Z2/Sigma, that "
            "must be derived from active currents, bulk stress and Sigma normals."
        ),
        "declared": declared,
        "readiness": readiness,
        "criteria": {
            "current": "J_n^Z2Sigma = J_n^+ + eps_Z2 J_n^- = 0",
            "stress_flux": "F_a^Z2Sigma = T^+_munu e_a^mu n_+^nu + eps_Z2 T^-_munu e_a^mu n_-^nu = 0",
            "route": "if current and stress criteria close, E_matterFlux = 0",
        },
        "closed": ["transparency_criteria_declared"],
        "still_open": [
            "active_embedding_ready",
            "Sigma_normals_ready",
            "no_normal_matter_current_ready",
            "bulk_stress_normal_flux_projection_ready",
            "Z2_bulk_stress_cancellation_ready",
            "active_Sigma_transparency_ready",
        ],
        "matter_flux_transparency_readiness_ledger_declared": all(declared.values()),
        "matter_flux_transparency_readiness_ready": all(declared.values()) and all(readiness.values()),
        "next_required": [
            "close_active_embedding_readiness_gate",
            "derive_Sigma_normals_from_active_embedding",
            "close_normal_matter_current_gate",
            "close_bulk_stress_normal_flux_cancellation_gate",
            "feed_transparency_to_matter_flux_frontier_gate",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Matter-Flux Transparency Readiness Gate",
        "",
        f"Active core: `{payload['active_core']}`",
        f"Ledger declared: `{payload['matter_flux_transparency_readiness_ledger_declared']}`",
        f"Readiness ready: `{payload['matter_flux_transparency_readiness_ready']}`",
        "",
        "## Criteria",
    ]
    lines.extend(f"- `{key}`: `{value}`" for key, value in payload["criteria"].items())
    lines.extend(["", "## Still Open"])
    lines.extend(f"- `{item}`" for item in payload["still_open"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
