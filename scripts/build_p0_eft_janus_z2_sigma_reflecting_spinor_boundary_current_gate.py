from __future__ import annotations

import json
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from scripts.build_p0_eft_janus_z2_sigma_spinor_boundary_projection_map_gate import (
    build_payload as build_spinor_boundary_projection_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_local_mit_reflecting_projector_gate import (
    build_payload as build_local_mit_projector_payload,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_reflecting_spinor_boundary_current_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_reflecting_spinor_boundary_current_gate.json")


def build_payload() -> dict:
    spinor_projection = build_spinor_boundary_projection_payload()
    local_mit = build_local_mit_projector_payload()
    declared = {
        "MIT_bag_boundary_current_bibliography_checked": True,
        "local_reflecting_boundary_condition_declared": True,
        "spinor_boundary_projection_map_gate_imported": True,
        "normal_Clifford_action_required": True,
        "no_free_boundary_phase": True,
        "observational_fit_forbidden": True,
    }
    closure = {
        "spinor_boundary_projection_map_ready": spinor_projection[
            "spinor_boundary_projection_map_ready"
        ],
        "Z2_normal_orientation_ready": spinor_projection["closure"][
            "Z2_normal_orientation_ready"
        ],
        "projection_idempotent_ready": spinor_projection["closure"]["projection_idempotent_ready"],
        "projection_self_adjoint_ready": spinor_projection["closure"]["projection_self_adjoint_ready"],
        "local_MIT_current_zero_algebra_ready": local_mit[
            "normal_current_zero_algebra_ready"
        ],
        "reflecting_boundary_condition_derived": False,
        "boundary_leakage_zero_derived": False,
        "normal_dirac_current_zero_derived": False,
    }
    return {
        "status": "janus-z2-sigma-reflecting-spinor-boundary-current-gate",
        "active_core": "Z2_tunnel_Sigma",
        "primary_sources_checked": [
            "MIT bag / reflecting Dirac boundary condition literature",
            "chiral MIT boundary condition normal-current references",
            "active Z2/Sigma spinor boundary projection map gate",
        ],
        "source_links": [
            "https://inspirehep.net/files/7326879becf517d363853f6037b27c8e",
            "https://academic.oup.com/ptep/article/2021/11/113B01/6380949",
            "https://arxiv.org/abs/1811.02947",
        ],
        "bibliography_result": (
            "Reflecting/MIT-type Dirac boundary conditions are a standard route to "
            "vanishing normal vector current. Active Janus Z2/Sigma still must derive "
            "the projector, normal Clifford action and zero-leakage condition; no "
            "free bag angle or fitted phase is allowed."
        ),
        "declared": declared,
        "closure": closure,
        "upstream_frontiers": {
            "spinor_boundary_projection": {
                "gate": spinor_projection["status"],
                "ready": spinor_projection["spinor_boundary_projection_map_ready"],
                "closure": spinor_projection["closure"],
            },
            "local_mit_reflecting_projector": {
                "gate": local_mit["status"],
                "ready": local_mit["local_mit_reflecting_projector_ready"],
                "scope": local_mit["scope"],
            },
        },
        "formulas": {
            "reflecting_current_condition": "J_n = psibar gamma(n) psi = 0",
            "projector_policy": "P_Z2Sigma must be idempotent, self-adjoint and phase-fixed",
            "local_algebra_scope": "MIT projector algebra only; physical boundary condition still must be derived",
            "transparency_link": "normal_dirac_current_zero -> J_n^Z2Sigma = 0 candidate",
        },
        "reflecting_spinor_boundary_current_ledger_declared": all(declared.values()),
        "normal_dirac_current_zero_ready": all(declared.values()) and all(closure.values()),
        "next_required": [
            "close_spinor_boundary_projection_map_gate",
            "derive_reflecting_boundary_condition_without_free_phase",
            "prove_boundary_leakage_zero",
            "feed_normal_dirac_current_zero_to_projected_dirac_normal_current_gate",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Reflecting Spinor Boundary Current Gate",
        "",
        f"Active core: `{payload['active_core']}`",
        f"Ledger declared: `{payload['reflecting_spinor_boundary_current_ledger_declared']}`",
        f"Normal current zero ready: `{payload['normal_dirac_current_zero_ready']}`",
        "",
        "## Formulae",
    ]
    lines.extend(f"- `{key}`: `{value}`" for key, value in payload["formulas"].items())
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
