from __future__ import annotations

import json
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from scripts.build_p0_eft_janus_z2_sigma_active_embedding_readiness_gate import (
    build_payload as build_active_embedding_readiness_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_plus_minus_matter_current_gate import (
    build_payload as build_plus_minus_matter_current_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_projected_dirac_normal_current_gate import (
    build_payload as build_projected_dirac_normal_current_payload,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_normal_matter_current_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_normal_matter_current_gate.json")


def build_payload() -> dict:
    active_embedding = build_active_embedding_readiness_payload()
    plus_minus_current = build_plus_minus_matter_current_payload()
    projected_normal = build_projected_dirac_normal_current_payload()
    declared = {
        "matter_current_bibliography_checked": True,
        "Noether_current_formula_imported": True,
        "plus_minus_matter_current_gate_declared": True,
        "projected_Dirac_matter_current_gate_declared": True,
        "projected_Dirac_normal_current_gate_declared": True,
        "normal_projection_criterion_declared": True,
        "Sigma_normals_required": True,
        "Z2_projected_current_declared": True,
        "observational_fit_forbidden": True,
    }
    closure = {
        "plus_matter_current_ready": plus_minus_current["closure"][
            "plus_current_ready"
        ],
        "minus_matter_current_ready": plus_minus_current["closure"][
            "minus_current_ready"
        ],
        "Sigma_normals_ready": active_embedding["readiness"]["unit_normals_ready"],
        "Z2_projected_normal_current_ready": projected_normal["closure"][
            "Z2_projected_normal_current_ready"
        ],
        "no_normal_matter_current_derived": projected_normal["closure"][
            "no_normal_matter_current_derived"
        ],
    }
    ready = all(declared.values()) and all(closure.values())
    primary_blocker = "none"
    if not ready:
        if not active_embedding["gate_passed"]:
            primary_blocker = active_embedding["primary_blocker"]
        elif not plus_minus_current.get("gate_passed", plus_minus_current["plus_minus_matter_current_ready"]):
            primary_blocker = plus_minus_current.get(
                "primary_blocker", "plus_minus_matter_current"
            )
        elif not projected_normal["gate_passed"]:
            primary_blocker = projected_normal["primary_blocker"]
        else:
            primary_blocker = "no_normal_matter_current_condition"
    return {
        "status": "janus-z2-sigma-normal-matter-current-gate",
        "active_core": "Z2_tunnel_Sigma",
        "primary_sources_checked": [
            "stress-energy/matter current normal-flux definitions",
            "thin-shell transparency no-normal-flux condition",
            "Dirac U(1) Noether current references for fermionic matter",
            "active plus/minus matter-current gate",
            "active projected Dirac matter-current gate",
            "active projected Dirac normal-current gate",
        ],
        "bibliography_result": (
            "Generic current conservation supplies a matter current and its normal "
            "projection. It does not supply the active Janus plus/minus current or "
            "the active Sigma normals."
        ),
        "declared": declared,
        "closure": closure,
        "upstream_frontiers": {
            "active_embedding": {
                "gate": active_embedding["status"],
                "ready": active_embedding["active_embedding_readiness_ready"],
                "primary_blocker": active_embedding["primary_blocker"],
                "readiness": active_embedding["readiness"],
            },
            "plus_minus_matter_current": {
                "gate": plus_minus_current["status"],
                "ready": plus_minus_current["plus_minus_matter_current_ready"],
                "primary_blocker": plus_minus_current.get("primary_blocker", "unknown"),
                "closure": plus_minus_current["closure"],
            },
            "projected_dirac_normal_current": {
                "gate": projected_normal["status"],
                "ready": projected_normal[
                    "projected_dirac_normal_current_ready"
                ],
                "no_normal_current_ready": projected_normal[
                    "no_normal_dirac_current_ready"
                ],
                "primary_blocker": projected_normal["primary_blocker"],
                "closure": projected_normal["closure"],
            },
        },
        "formula": {
            "normal_current_plus": "J_n^+ = J_mu^+ n_+^mu",
            "normal_current_minus": "J_n^- = J_mu^- n_-^mu",
            "z2_projected_normal_current": "J_n^Z2Sigma = J_n^+ + eps_Z2 J_n^-",
            "no_normal_current": "J_n^Z2Sigma = 0",
        },
        "normal_matter_current_ledger_declared": all(declared.values()),
        "no_normal_matter_current_ready": ready,
        "gate_passed": ready,
        "primary_blocker": primary_blocker,
        "next_required": [
            "derive_plus_minus_matter_currents_from_active_matter_action",
            "pass_plus_minus_matter_current_gate",
            "pass_projected_Dirac_matter_current_gate",
            "pass_projected_Dirac_normal_current_gate",
            "pass_tangent_normal_orientation_gate",
            "project_currents_on_Sigma_normals",
            "prove_or_reject_J_n_Z2Sigma_equals_zero",
            "feed_result_to_matter_flux_transparency_gate",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Normal Matter Current Gate",
        "",
        f"Active core: `{payload['active_core']}`",
        f"Ledger declared: `{payload['normal_matter_current_ledger_declared']}`",
        f"No-normal-current ready: `{payload['no_normal_matter_current_ready']}`",
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
