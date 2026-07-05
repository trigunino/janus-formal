from __future__ import annotations

import json
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from scripts.build_p0_eft_janus_z2_sigma_reflecting_spinor_boundary_current_gate import (
    build_payload as build_reflecting_boundary_current_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_active_embedding_readiness_gate import (
    build_payload as build_active_embedding_readiness_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_projected_dirac_matter_current_gate import (
    build_payload as build_projected_dirac_matter_current_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_dirac_normal_current_z2_cancellation_gate import (
    build_payload as build_z2_current_cancellation_payload,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_projected_dirac_normal_current_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_projected_dirac_normal_current_gate.json")


def build_payload() -> dict:
    reflecting = build_reflecting_boundary_current_payload()
    active_embedding = build_active_embedding_readiness_payload()
    projected_current = build_projected_dirac_matter_current_payload()
    z2_cancellation = build_z2_current_cancellation_payload()
    declared = {
        "thin_shell_flux_bibliography_checked": True,
        "projected_Dirac_matter_current_gate_declared": True,
        "reflecting_spinor_boundary_current_gate_declared": True,
        "tangent_normal_orientation_gate_declared": True,
        "plus_normal_current_declared": True,
        "minus_normal_current_declared": True,
        "Z2_projected_normal_current_declared": True,
        "no_fit_transparency_decision": True,
        "observational_fit_forbidden": True,
    }
    closure = {
        "projected_Dirac_matter_current_ready": projected_current[
            "projected_dirac_matter_current_ready"
        ],
        "Sigma_normals_ready": active_embedding["readiness"]["unit_normals_ready"],
        "plus_normal_current_ready": (
            projected_current["projected_dirac_matter_current_ready"]
            and active_embedding["readiness"]["unit_normals_ready"]
        ),
        "minus_normal_current_ready": (
            projected_current["projected_dirac_matter_current_ready"]
            and active_embedding["readiness"]["unit_normals_ready"]
        ),
        "Z2_projected_normal_current_ready": (
            projected_current["projected_dirac_matter_current_ready"]
            and active_embedding["readiness"]["unit_normals_ready"]
        ),
        "reflecting_boundary_normal_current_zero_ready": reflecting[
            "normal_dirac_current_zero_ready"
        ],
        "Z2_current_cancellation_ready": z2_cancellation[
            "dirac_normal_current_z2_cancellation_ready"
        ],
        "no_normal_matter_current_derived": reflecting[
            "normal_dirac_current_zero_ready"
        ] or z2_cancellation["dirac_normal_current_z2_cancellation_ready"],
    }
    normal_zero_route_ready = (
        closure["reflecting_boundary_normal_current_zero_ready"]
        or closure["Z2_current_cancellation_ready"]
    )
    projection_slots_ready = (
        closure["projected_Dirac_matter_current_ready"]
        and closure["Sigma_normals_ready"]
        and closure["plus_normal_current_ready"]
        and closure["minus_normal_current_ready"]
        and closure["Z2_projected_normal_current_ready"]
    )
    ready = all(declared.values()) and projection_slots_ready and normal_zero_route_ready
    primary_blocker = "none"
    if not ready:
        if not active_embedding["gate_passed"]:
            primary_blocker = active_embedding["primary_blocker"]
        elif not projected_current["gate_passed"]:
            primary_blocker = projected_current["primary_blocker"]
        elif not reflecting.get("gate_passed", reflecting["normal_dirac_current_zero_ready"]):
            primary_blocker = reflecting.get(
                "primary_blocker", "reflecting_spinor_boundary_current"
            )
        else:
            primary_blocker = "projected_Dirac_normal_current_zero_condition"
    return {
        "status": "janus-z2-sigma-projected-dirac-normal-current-gate",
        "active_core": "Z2_tunnel_Sigma",
        "primary_sources_checked": [
            "thin-shell conservation identity with normal momentum flux",
            "Dirac U(1) Noether current normal projection",
            "active projected Dirac matter-current and tangent/normal gates",
            "active reflecting spinor boundary-current gate",
        ],
        "bibliography_result": (
            "Thin-shell literature supplies the normal-flux slot and Dirac theory "
            "supplies the current. The active Z2/Sigma cancellation or leakage "
            "must still be derived from the projected current and Sigma normals."
        ),
        "source_links": [
            "https://link.aps.org/doi/10.1103/PhysRevD.101.124035",
            "https://arxiv.org/html/2503.03918v2",
            "https://arxiv.org/pdf/1201.5423",
            "https://doi.org/10.1007/BF02710419",
            "https://cosmo.fis.fc.ul.pt/~crawford/papers/cqg204034p17.pdf",
        ],
        "declared": declared,
        "closure": closure,
        "upstream_frontiers": {
            "reflecting_spinor_boundary_current": {
                "gate": reflecting["status"],
                "ready": reflecting["normal_dirac_current_zero_ready"],
                "primary_blocker": reflecting.get("primary_blocker", "unknown"),
                "closure": reflecting["closure"],
            },
            "active_embedding": {
                "gate": active_embedding["status"],
                "ready": active_embedding["active_embedding_readiness_ready"],
                "primary_blocker": active_embedding["primary_blocker"],
                "readiness": active_embedding["readiness"],
            },
            "projected_dirac_matter_current": {
                "gate": projected_current["status"],
                "ready": projected_current["projected_dirac_matter_current_ready"],
                "primary_blocker": projected_current["primary_blocker"],
                "closure": projected_current["closure"],
            },
            "z2_current_cancellation": {
                "gate": z2_cancellation["status"],
                "ready": z2_cancellation["dirac_normal_current_z2_cancellation_ready"],
                "primary_blocker": z2_cancellation["primary_blocker"],
                "route_blockers": z2_cancellation.get("route_blockers", []),
                "closure": z2_cancellation["closure"],
            },
        },
        "formulas": {
            "plus_normal_current": "J_n^+ = J_+^mu n_mu^+",
            "minus_normal_current": "J_n^- = J_-^mu n_mu^-",
            "z2_projected_normal_current": "J_n^Z2Sigma = J_n^+ + eps_Z2 J_n^-",
            "transparency_test": "transparent Dirac branch requires J_n^Z2Sigma = 0",
            "z2_cancellation_route": "derive current parity sigma_J and projected-current sign, then J_n^+ + eps_current J_n^- = 0",
        },
        "projected_dirac_normal_current_ledger_declared": all(declared.values()),
        "projected_dirac_normal_current_ready": all(declared.values()) and projection_slots_ready,
        "no_normal_dirac_current_ready": ready,
        "gate_passed": ready,
        "primary_blocker": primary_blocker,
        "next_required": [
            "pass_projected_Dirac_matter_current_gate",
            "pass_tangent_normal_orientation_gate",
            "project_J_plus_and_J_minus_on_Sigma_normals",
            "derive_or_reject_J_n_Z2Sigma_equals_zero",
            "or_close_reflecting_spinor_boundary_current_gate",
            "or_close_Dirac_normal_current_Z2_cancellation_gate",
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
