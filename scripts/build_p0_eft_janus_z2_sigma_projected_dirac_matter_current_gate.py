from __future__ import annotations

import json
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from scripts.build_p0_eft_janus_z2_sigma_plus_minus_matter_current_gate import (
    build_payload as build_plus_minus_matter_current_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_projected_dirac_action_reduction_gate import (
    build_payload as build_projected_dirac_action_payload,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_projected_dirac_matter_current_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_projected_dirac_matter_current_gate.json")


def build_payload() -> dict:
    projected_action = build_projected_dirac_action_payload()
    plus_minus_current = build_plus_minus_matter_current_payload()
    declared = {
        "Dirac_Noether_current_bibliography_checked": True,
        "projected_Dirac_action_reduction_gate_declared": True,
        "U1_vector_symmetry_declared": True,
        "plus_current_formula_declared": True,
        "minus_current_formula_declared": True,
        "Z2_projected_current_declared": True,
        "covariant_conservation_guard_declared": True,
        "observational_fit_forbidden": True,
    }
    closure = {
        "projected_Dirac_action_ready": projected_action[
            "projected_dirac_action_reduction_ready"
        ],
        "plus_current_ready": plus_minus_current["closure"]["plus_current_ready"],
        "minus_current_ready": plus_minus_current["closure"]["minus_current_ready"],
        "Z2_projected_current_ready": (
            projected_action["closure"]["Z2_projected_Dirac_action_ready"]
            and plus_minus_current["closure"]["plus_minus_matter_currents_ready"]
        ),
        "plus_minus_matter_currents_ready": plus_minus_current[
            "plus_minus_matter_current_ready"
        ],
    }
    ready = all(declared.values()) and all(closure.values())
    primary_blocker = "none"
    if not ready:
        if not projected_action["projected_dirac_action_reduction_ready"]:
            primary_blocker = projected_action.get(
                "primary_blocker", "projected_Dirac_action_reduction"
            )
        elif not plus_minus_current["plus_minus_matter_current_ready"]:
            primary_blocker = plus_minus_current.get(
                "primary_blocker", "plus_minus_matter_current"
            )
        else:
            primary_blocker = "Z2_projected_current"
    return {
        "status": "janus-z2-sigma-projected-dirac-matter-current-gate",
        "active_core": "Z2_tunnel_Sigma",
        "primary_sources_checked": [
            "Dirac U(1) vector symmetry and Noether current",
            "curved-spacetime Dirac equation with tetrad/spin connection",
            "Holst/Einstein-Cartan fermion coupling context",
            "active projected Dirac action reduction gate",
        ],
        "bibliography_result": (
            "Generic Dirac theory supplies the vector Noether current. It does "
            "not supply the active Z2/Sigma projected current before the "
            "projected Dirac action is reduced."
        ),
        "source_links": [
            "https://arxiv.org/html/2503.03918v2",
            "https://link.aps.org/doi/10.1103/PhysRevD.79.064029",
            "https://arxiv.org/pdf/1201.5423",
            "https://s3.cern.ch/inspire-prod-files-d/d0a75bfac1295febe61b60f90aef7505",
        ],
        "declared": declared,
        "closure": closure,
        "upstream_frontiers": {
            "projected_dirac_action_reduction": {
                "gate": projected_action["status"],
                "ready": projected_action["projected_dirac_action_reduction_ready"],
                "primary_blocker": projected_action.get("primary_blocker", "unknown"),
                "closure": projected_action["closure"],
                "next_required": projected_action["next_required"],
            },
            "plus_minus_matter_current": {
                "gate": plus_minus_current["status"],
                "ready": plus_minus_current["plus_minus_matter_current_ready"],
                "primary_blocker": plus_minus_current.get("primary_blocker", "unknown"),
                "closure": plus_minus_current["closure"],
                "next_required": plus_minus_current["next_required"],
            },
        },
        "formulas": {
            "plus_current": "J_+^mu = psi_bar_+ gamma_+^mu psi_+",
            "minus_current": "J_-^mu = psi_bar_- gamma_-^mu psi_-",
            "projected_current": "J_Z2Sigma^mu = P_Z2Sigma(J_+^mu, J_-^mu; psi_Sigma^Z2)",
            "conservation_guard": "nabla_mu J_Z2Sigma^mu = 0 unless active Sigma leakage/anomaly is derived",
        },
        "projected_dirac_matter_current_ledger_declared": all(declared.values()),
        "projected_dirac_matter_current_ready": ready,
        "gate_passed": ready,
        "primary_blocker": primary_blocker,
        "next_required": [
            "pass_projected_Dirac_action_reduction_gate",
            "derive_plus_current_from_projected_Dirac_action",
            "derive_minus_current_from_projected_Dirac_action",
            "derive_Z2_projected_current",
            "feed_projected_current_to_normal_matter_current_gate",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Projected Dirac Matter Current Gate",
        "",
        f"Active core: `{payload['active_core']}`",
        f"Ledger declared: `{payload['projected_dirac_matter_current_ledger_declared']}`",
        f"Current ready: `{payload['projected_dirac_matter_current_ready']}`",
        f"Primary blocker: `{payload['primary_blocker']}`",
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
