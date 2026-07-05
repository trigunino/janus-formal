from __future__ import annotations

import json
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from scripts.build_p0_eft_janus_z2_sigma_flux_projection_domain_gate import (
    build_payload as build_flux_projection_domain_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_bulk_stress_normal_flux_cancellation_gate import (
    build_payload as build_bulk_stress_flux_payload,
)

REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_matter_flux_active_projection_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_matter_flux_active_projection_gate.json")


def build_payload() -> dict:
    domain = build_flux_projection_domain_payload()
    bulk_stress_flux = build_bulk_stress_flux_payload()
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
    bulk_closure = bulk_stress_flux["closure"]
    closure = {
        "plus_bulk_stress_of_a_ready": bulk_closure["bulk_stress_plus_of_a_ready"],
        "minus_bulk_stress_of_a_ready": bulk_closure["bulk_stress_minus_of_a_ready"],
        "flux_projection_domain_ready": domain["flux_projection_domain_ready"],
        "embedding_of_a_ready": domain["closure"]["embedding_of_a_ready"],
        "Sigma_tangents_ready": domain["closure"]["Sigma_tangents_ready"],
        "Sigma_normals_ready": domain["closure"]["Sigma_normals_ready"],
        "active_flux_of_a_ready": bulk_stress_flux[
            "bulk_stress_normal_flux_projection_ready"
        ],
    }
    ready = all(declared.values()) and all(closure.values())
    primary_blocker = (
        "none"
        if ready
        else bulk_stress_flux.get("primary_blocker")
        or domain.get("primary_blocker")
        or "bulk_stress_of_a"
    )
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
        "upstream_frontiers": {
            "flux_projection_domain": {
                "gate": domain["status"],
                "ready": domain["flux_projection_domain_ready"],
                "closure": domain["closure"],
                "primary_blocker": domain.get("primary_blocker"),
            },
            "bulk_stress_normal_flux": {
                "gate": bulk_stress_flux["status"],
                "projection_ready": bulk_stress_flux[
                    "bulk_stress_normal_flux_projection_ready"
                ],
                "cancellation_ready": bulk_stress_flux[
                    "bulk_stress_normal_flux_cancellation_ready"
                ],
                "closure": bulk_stress_flux["closure"],
                "primary_blocker": bulk_stress_flux.get("primary_blocker"),
            },
        },
        "formula": {
            "plus_flux": "F_a^+ = T_munu^+ e_a^mu n_+^nu",
            "minus_flux": "F_a^- = T_munu^- e_a^mu n_-^nu",
            "net_flux": "F_a^Z2Sigma = F_a^+ + eps_Z2 F_a^-",
        },
        "active_flux_projection_ledger_declared": all(declared.values()),
        "active_flux_projection_ready": ready,
        "gate_passed": ready,
        "primary_blocker": primary_blocker,
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
