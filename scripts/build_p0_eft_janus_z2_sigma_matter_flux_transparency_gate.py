from __future__ import annotations

import json
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from scripts.build_p0_eft_janus_z2_sigma_bulk_stress_normal_flux_cancellation_gate import (
    build_payload as build_bulk_stress_flux_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_normal_matter_current_gate import (
    build_payload as build_normal_matter_current_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_normal_matter_current_readiness_gate import (
    build_payload as build_normal_matter_current_readiness_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_projected_dirac_normal_current_gate import (
    build_payload as build_projected_dirac_normal_current_payload,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_matter_flux_transparency_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_matter_flux_transparency_gate.json")


def build_payload() -> dict:
    normal_current = build_normal_matter_current_payload()
    normal_current_readiness = build_normal_matter_current_readiness_payload()
    dirac_normal_current = build_projected_dirac_normal_current_payload()
    bulk_stress_flux = build_bulk_stress_flux_payload()
    criteria = {
        "thin_shell_transparency_bibliography_checked": True,
        "no_normal_matter_current_criterion_declared": True,
        "normal_matter_current_gate_declared": True,
        "projected_Dirac_normal_current_gate_declared": True,
        "bulk_stress_normal_flux_cancellation_gate_declared": True,
        "bulk_stress_normal_projection_criterion_declared": True,
        "Sigma_as_geometric_throat_not_matter_portal_declared": True,
        "Z2_flux_cancellation_criterion_declared": True,
        "observational_fit_forbidden": True,
        "transparency_sufficient_conditions_declared": True,
    }
    no_normal_current = (
        normal_current["closure"]["no_normal_matter_current_derived"]
        or dirac_normal_current["closure"]["no_normal_matter_current_derived"]
    )
    transparent_stress = (
        bulk_stress_flux["closure"]["bulk_stress_normal_projection_zero_derived"]
        or bulk_stress_flux["closure"]["Z2_flux_cancellation_derived"]
    )
    closure = {
        "normal_matter_current_readiness_ready": normal_current_readiness[
            "normal_matter_current_readiness_ready"
        ],
        "normal_matter_current_gate_ready": normal_current[
            "no_normal_matter_current_ready"
        ],
        "projected_dirac_normal_current_ready": dirac_normal_current[
            "projected_dirac_normal_current_ready"
        ],
        "no_normal_matter_current_derived": no_normal_current,
        "bulk_stress_normal_flux_projection_ready": bulk_stress_flux[
            "bulk_stress_normal_flux_projection_ready"
        ],
        "bulk_stress_normal_projection_zero_derived": bulk_stress_flux["closure"][
            "bulk_stress_normal_projection_zero_derived"
        ],
        "Z2_flux_cancellation_derived": bulk_stress_flux["closure"][
            "Z2_flux_cancellation_derived"
        ],
        "active_Sigma_transparency_derived": no_normal_current and transparent_stress,
    }
    active_sigma_transparency_ready = (
        all(criteria.values())
        and closure["normal_matter_current_readiness_ready"]
        and closure["normal_matter_current_gate_ready"]
        and closure["projected_dirac_normal_current_ready"]
        and closure["no_normal_matter_current_derived"]
        and closure["bulk_stress_normal_flux_projection_ready"]
        and (
            closure["bulk_stress_normal_projection_zero_derived"]
            or closure["Z2_flux_cancellation_derived"]
        )
        and closure["active_Sigma_transparency_derived"]
    )
    nearest_transparency_subfrontier = {
        "block": normal_current_readiness.get(
            "primary_blocker", "normal_matter_current"
        ),
        "gate": "P0EFTJanusZ2SigmaNormalMatterCurrentReadinessGate",
        "required": [
            "derive active embedding and Sigma normals",
            "derive plus/minus or projected Dirac matter currents",
            "project currents on Sigma normals",
            "prove or reject J_n^Z2Sigma = 0",
        ],
        "diagnostic_only": True,
    }
    return {
        "status": "janus-z2-sigma-matter-flux-transparency-gate",
        "active_core": "Z2_tunnel_Sigma",
        "primary_sources_checked": [
            "Poisson-Visser transparent thin-shell wormhole branch",
            "Thin-shell surface conservation identity with momentum flux term",
            "Dynamic thin-shell literature using no energy-momentum flux across shell",
            "active normal-matter-current gate",
            "active projected Dirac normal-current gate",
            "active bulk-stress normal-flux cancellation gate",
        ],
        "bibliography_result": (
            "Transparency is a standard branch when no matter/radiation crosses the shell. "
            "For active Janus/Sigma it must be derived from vanishing normal matter current, "
            "zero normal bulk-stress projection, or exact Z2 flux cancellation."
        ),
        "criteria": criteria,
        "closure": closure,
        "upstream_frontiers": {
            "normal_matter_current": {
                "gate": normal_current["status"],
                "ready": normal_current["no_normal_matter_current_ready"],
                "primary_blocker": normal_current.get("primary_blocker", "unknown"),
                "closure": normal_current["closure"],
            },
            "normal_matter_current_readiness": {
                "gate": normal_current_readiness["status"],
                "ready": normal_current_readiness[
                    "normal_matter_current_readiness_ready"
                ],
                "primary_blocker": normal_current_readiness.get("primary_blocker", "unknown"),
                "still_open": normal_current_readiness["still_open"],
            },
            "projected_dirac_normal_current": {
                "gate": dirac_normal_current["status"],
                "normal_current_ready": dirac_normal_current[
                    "projected_dirac_normal_current_ready"
                ],
                "no_normal_current_ready": dirac_normal_current[
                    "no_normal_dirac_current_ready"
                ],
                "primary_blocker": dirac_normal_current.get("primary_blocker", "unknown"),
                "closure": dirac_normal_current["closure"],
            },
            "bulk_stress_flux": {
                "gate": bulk_stress_flux["status"],
                "projection_ready": bulk_stress_flux[
                    "bulk_stress_normal_flux_projection_ready"
                ],
                "cancellation_ready": bulk_stress_flux[
                    "bulk_stress_normal_flux_cancellation_ready"
                ],
                "primary_blocker": bulk_stress_flux.get("primary_blocker", "unknown"),
                "closure": bulk_stress_flux["closure"],
            },
        },
        "sufficient_condition": (
            "F_a^Z2Sigma = T_munu^+ e_a^mu n_+^nu + eps_Z2 T_munu^- e_a^mu n_-^nu = 0"
        ),
        "transparency_criteria_declared": all(criteria.values()),
        "active_sigma_transparency_ready": active_sigma_transparency_ready,
        "gate_passed": active_sigma_transparency_ready,
        "primary_blocker": (
            "none"
            if active_sigma_transparency_ready
            else (
                normal_current_readiness.get(
                    "primary_blocker",
                    normal_current.get(
                        "primary_blocker",
                        dirac_normal_current.get(
                            "primary_blocker", "normal_matter_current"
                        ),
                    ),
                )
                if not closure["no_normal_matter_current_derived"]
                else bulk_stress_flux.get(
                    "primary_blocker", "bulk_stress_normal_flux_cancellation"
                )
            )
        ),
        "current_frontier": [
            f"{key} = false"
            for key, ready in closure.items()
            if not ready
        ],
        "nearest_transparency_subfrontier": nearest_transparency_subfrontier,
        "nearest_transparency_subfrontier_declared": True,
        "nearest_transparency_subfrontier_diagnostic_only": True,
        "next_required": [
            "derive_no_normal_matter_current_at_Sigma",
            "pass_normal_matter_current_gate",
            "pass_projected_Dirac_normal_current_gate",
            "pass_bulk_stress_normal_flux_cancellation_gate",
            "derive_bulk_stress_normal_projection_zero_or_Z2_cancellation",
            "if_transparency_fails_compute_active_flux_F_a_of_a",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Matter-Flux Transparency Gate",
        "",
        f"Active core: `{payload['active_core']}`",
        f"Criteria declared: `{payload['transparency_criteria_declared']}`",
        f"Transparency ready: `{payload['active_sigma_transparency_ready']}`",
        "",
        "## Sufficient Condition",
        f"`{payload['sufficient_condition']}`",
        "",
        "## Current Frontier",
    ]
    lines.extend(f"- `{item}`" for item in payload["current_frontier"])
    lines.extend(["", "## Nearest Transparency Subfrontier"])
    nearest = payload["nearest_transparency_subfrontier"]
    lines.append(f"- `block`: `{nearest['block']}`")
    lines.append(f"- `gate`: `{nearest['gate']}`")
    lines.extend(f"- `required`: `{item}`" for item in nearest["required"])
    lines.extend([
        "",
        "## Next Required",
    ])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
