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
from scripts.build_p0_eft_janus_z2_sigma_projected_dirac_matter_current_gate import (
    build_payload as build_projected_dirac_matter_current_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_projected_dirac_normal_current_gate import (
    build_payload as build_projected_dirac_normal_current_payload,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_normal_matter_current_readiness_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_normal_matter_current_readiness_gate.json")


def build_payload() -> dict:
    active_embedding = build_active_embedding_readiness_payload()
    projected_current = build_projected_dirac_matter_current_payload()
    projected_normal = build_projected_dirac_normal_current_payload()
    declared = {
        "normal_matter_current_gate_imported": True,
        "plus_minus_matter_current_gate_imported": True,
        "projected_Dirac_matter_current_gate_imported": True,
        "projected_Dirac_normal_current_gate_imported": True,
        "active_embedding_readiness_gate_imported": True,
        "Dirac_Noether_current_bibliography_checked": True,
    }
    readiness = {
        "active_embedding_ready": active_embedding["active_embedding_readiness_ready"],
        "Sigma_normals_ready": active_embedding["readiness"]["unit_normals_ready"],
        "plus_minus_matter_currents_ready": projected_current["closure"][
            "plus_minus_matter_currents_ready"
        ],
        "projected_Dirac_matter_current_ready": projected_current[
            "projected_dirac_matter_current_ready"
        ],
        "projected_Dirac_normal_current_ready": projected_normal[
            "projected_dirac_normal_current_ready"
        ],
        "no_normal_matter_current_derived": projected_normal["closure"][
            "no_normal_matter_current_derived"
        ],
        "no_normal_matter_current_ready": projected_normal[
            "no_normal_dirac_current_ready"
        ],
    }
    ready = all(declared.values()) and all(readiness.values())
    primary_blocker = "none"
    if not ready:
        if not active_embedding["gate_passed"]:
            primary_blocker = active_embedding["primary_blocker"]
        elif not projected_current["gate_passed"]:
            primary_blocker = projected_current["primary_blocker"]
        elif not projected_normal["gate_passed"]:
            primary_blocker = projected_normal["primary_blocker"]
        else:
            primary_blocker = "normal_matter_current_zero_condition"
    nearest_normal_current_frontier = {
        "block": primary_blocker,
        "gate": "P0EFTJanusZ2SigmaActiveEmbeddingReadinessGate",
        "required": [
            "derive R_Sigma(a) from the throat variational equation",
            "derive X_+/- (a) from the conditional embedding map",
            "transport Sigma unit normals from the active embedding",
            "then project plus/minus Dirac currents on Sigma normals",
        ],
        "diagnostic_only": True,
    }
    return {
        "status": "janus-z2-sigma-normal-matter-current-readiness-gate",
        "active_core": "Z2_tunnel_Sigma",
        "primary_sources_checked": [
            "Dirac U(1) Noether current",
            "curved-spacetime Dirac equation with tetrad/spin connection",
            "thin-shell normal-flux projection",
        ],
        "source_links": [
            "https://arxiv.org/html/2503.03918v2",
            "https://s3.cern.ch/inspire-prod-files-d/d0a75bfac1295febe61b60f90aef7505",
            "https://doi.org/10.1007/BF02710419",
        ],
        "bibliography_result": (
            "Generic Dirac theory supplies J^mu = psibar gamma^mu psi and its "
            "normal projection. Janus Z2/Sigma still needs the active projected "
            "current and active Sigma normals before J_n^Z2Sigma can be tested."
        ),
        "declared": declared,
        "readiness": readiness,
        "upstream_frontiers": {
            "active_embedding": {
                "gate": active_embedding["status"],
                "ready": active_embedding["active_embedding_readiness_ready"],
                "primary_blocker": active_embedding["primary_blocker"],
                "readiness": active_embedding["readiness"],
                "nearest_frontier": active_embedding["nearest_embedding_frontier"],
            },
            "projected_dirac_matter_current": {
                "gate": projected_current["status"],
                "ready": projected_current["projected_dirac_matter_current_ready"],
                "primary_blocker": projected_current["primary_blocker"],
                "closure": projected_current["closure"],
                "next_required": projected_current["next_required"],
            },
            "projected_dirac_normal_current": {
                "gate": projected_normal["status"],
                "ready": projected_normal["projected_dirac_normal_current_ready"],
                "no_normal_current_ready": projected_normal[
                    "no_normal_dirac_current_ready"
                ],
                "primary_blocker": projected_normal["primary_blocker"],
                "closure": projected_normal["closure"],
                "next_required": projected_normal["next_required"],
            },
        },
        "formulae": {
            "dirac_current": "J_pm^mu = psibar_pm gamma_pm^mu psi_pm",
            "normal_projection": "J_n^pm = J_pm^mu n_mu^pm",
            "z2_current": "J_n^Z2Sigma = J_n^+ + eps_Z2 J_n^-",
            "transparency_test": "J_n^Z2Sigma = 0",
        },
        "closed": [
            "Dirac_Noether_current_formula_declared",
            "normal_projection_formula_declared",
        ],
        "still_open": [
            "active_embedding_ready",
            "Sigma_normals_ready",
            "plus_minus_matter_currents_ready",
            "projected_Dirac_matter_current_ready",
            "projected_Dirac_normal_current_ready",
            "no_normal_matter_current_derived",
        ],
        "nearest_normal_current_frontier": nearest_normal_current_frontier,
        "nearest_normal_current_frontier_declared": True,
        "nearest_normal_current_frontier_diagnostic_only": True,
        "normal_matter_current_readiness_ledger_declared": all(declared.values()),
        "normal_matter_current_readiness_ready": ready,
        "gate_passed": ready,
        "primary_blocker": primary_blocker,
        "next_required": [
            "close_active_embedding_readiness_gate",
            "close_projected_Dirac_matter_current_gate",
            "project_currents_on_active_Sigma_normals",
            "prove_or_reject_J_n_Z2Sigma_equals_zero",
            "feed_no_normal_current_to_transparency_readiness_gate",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Normal Matter Current Readiness Gate",
        "",
        f"Active core: `{payload['active_core']}`",
        f"Ledger declared: `{payload['normal_matter_current_readiness_ledger_declared']}`",
        f"Readiness ready: `{payload['normal_matter_current_readiness_ready']}`",
        "",
        "## Formulae",
    ]
    lines.extend(f"- `{key}`: `{value}`" for key, value in payload["formulae"].items())
    lines.extend(["", "## Still Open"])
    lines.extend(f"- `{item}`" for item in payload["still_open"])
    lines.extend(["", "## Nearest Normal-Current Frontier"])
    nearest = payload["nearest_normal_current_frontier"]
    lines.append(f"- `block`: `{nearest['block']}`")
    lines.append(f"- `gate`: `{nearest['gate']}`")
    lines.extend(f"- `required`: `{item}`" for item in nearest["required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
