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
from scripts.build_p0_eft_janus_sigma_boundary_variational_decomposition_gate import (
    build_payload as build_boundary_variation_payload,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_reflecting_spinor_boundary_current_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_reflecting_spinor_boundary_current_gate.json")


def build_payload() -> dict:
    spinor_projection = build_spinor_boundary_projection_payload()
    local_mit = build_local_mit_projector_payload()
    boundary_variation = build_boundary_variation_payload()
    local_reflecting_boundary_condition_derived = (
        boundary_variation["sigma_boundary_variational_package_declared"]
        and local_mit["local_mit_reflecting_projector_ready"]
        and local_mit["closure"]["projection_idempotent_ready"]
        and local_mit["closure"]["projection_self_adjoint_ready"]
        and local_mit["declared"]["projector_phase_fixed"]
    )
    local_boundary_leakage_zero_derived = (
        local_reflecting_boundary_condition_derived
        and local_mit["normal_current_zero_algebra_ready"]
    )
    declared = {
        "MIT_bag_boundary_current_bibliography_checked": True,
        "local_reflecting_boundary_condition_declared": True,
        "sigma_boundary_variation_imported": boundary_variation[
            "sigma_boundary_variational_package_declared"
        ],
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
        "local_reflecting_boundary_condition_derived": local_reflecting_boundary_condition_derived,
        "local_boundary_leakage_zero_derived": local_boundary_leakage_zero_derived,
        "reflecting_boundary_condition_derived": local_reflecting_boundary_condition_derived,
        "boundary_leakage_zero_derived": local_boundary_leakage_zero_derived,
        "normal_dirac_current_zero_derived": (
            local_boundary_leakage_zero_derived
            and spinor_projection["spinor_boundary_projection_map_ready"]
        ),
    }
    local_normal_current_zero_ready = (
        all(declared.values()) and local_boundary_leakage_zero_derived
    )
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
            "the global spinor projection map before a projected normal current can be "
            "claimed; no free bag angle or fitted phase is allowed."
        ),
        "declared": declared,
        "closure": closure,
        "upstream_frontiers": {
            "sigma_boundary_variation": {
                "gate": boundary_variation["status"],
                "ready": boundary_variation["sigma_boundary_variational_package_declared"],
                "full_boundary_action_closed_on_sigma": boundary_variation[
                    "full_boundary_action_closed_on_sigma"
                ],
            },
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
            "local_algebra_scope": "local reflecting boundary condition derived; global Z2Sigma spinor projection still open",
            "variation_route": "Sigma boundary variational package + phase-fixed self-adjoint local projector -> reflecting boundary condition locally",
            "transparency_link": "normal_dirac_current_zero -> J_n^Z2Sigma = 0 candidate",
        },
        "reflecting_spinor_boundary_current_ledger_declared": all(declared.values()),
        "local_normal_dirac_current_zero_ready": local_normal_current_zero_ready,
        "normal_dirac_current_zero_ready": all(declared.values()) and all(closure.values()),
        "primary_blocker": (
            "none"
            if all(declared.values()) and all(closure.values())
            else "spinor_boundary_projection_map_ready"
        ),
        "next_required": [
            "close_spinor_boundary_projection_map_gate",
            "derive_global_Z2Sigma_spinor_projection_map",
            "derive_boundary_spinor_restriction_data",
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
        f"Local normal current zero ready: `{payload['local_normal_dirac_current_zero_ready']}`",
        f"Normal current zero ready: `{payload['normal_dirac_current_zero_ready']}`",
        f"Primary blocker: `{payload['primary_blocker']}`",
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
