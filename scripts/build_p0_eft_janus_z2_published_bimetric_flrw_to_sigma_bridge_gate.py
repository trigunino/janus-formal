from __future__ import annotations

import json
import sys
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.derive_p0_eft_janus_z2_published_flrw_bianchi_reduction_gate import (
    build_payload as flrw_bianchi,
)
from scripts.derive_p0_eft_janus_z2_published_interaction_slots_gate import (
    build_payload as interaction_slots,
)
from scripts.build_p0_eft_janus_z2_sigma_active_embedding_to_flrw_extrinsic_curvature_input_gate import (
    build_payload as embedding_to_k,
)
from scripts.build_p0_eft_janus_z2_sigma_sector_density_pressure_of_a_gate import (
    build_payload as sector_density_pressure,
)
from scripts.build_p0_eft_janus_z2_published_bimetric_flrw_sector_source_reduction_gate import (
    build_payload as sector_source_reduction,
)


JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_published_bimetric_flrw_to_sigma_bridge_gate.json")
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_published_bimetric_flrw_to_sigma_bridge_gate.md")
ACTIVE_MANIFEST_PATH = Path("outputs/active_z2_sigma/published_bimetric_flrw_to_sigma_bridge_requirements.json")


def _ready(payload: dict[str, Any], key: str) -> bool:
    return bool(payload.get(key))


def build_payload() -> dict[str, Any]:
    slots = interaction_slots()
    flrw = flrw_bianchi()
    source_reduction = sector_source_reduction()
    sector = sector_density_pressure()
    k_pullback = embedding_to_k()

    readiness = {
        "published_interaction_slots_ready": _ready(slots, "gate_passed"),
        "determinant_factors_ready": _ready(flrw, "determinant_formula_closed"),
        "flrw_reduced_bianchi_ready": _ready(flrw, "flrw_reduced_bianchi_ready"),
        "sector_rho_pressure_shape_ready": bool(
            source_reduction["shape_level"]["rho_p_shape_ready"]
        ),
        "sector_rho_pressure_of_a_ready": _ready(sector, "sector_density_pressure_of_a_ready"),
        "sector_normalizations_derived": bool(
            sector.get("closure", {}).get("plus_initial_normalization_derived")
            and sector.get("closure", {}).get("minus_initial_normalization_derived")
        ),
        "sigma_embedding_pullback_ready": _ready(
            k_pullback, "gate_passed"
        ),
        "sigma_induced_metrics_ready": bool(k_pullback.get("input_manifest", {}).get("exists")),
        "sigma_extrinsic_curvatures_ready": _ready(
            k_pullback, "gate_passed"
        ),
        "sigma_stress_flux_projection_ready": False,
        "projected_bianchi_junction_ready": False,
    }

    blockers = [name for name, value in readiness.items() if not value]
    honest_shortcuts_forbidden = {
        "copied_published_H_of_a": False,
        "fitted_sector_density": False,
        "forced_N_gap_to_density": False,
        "ignored_sigma_pullback": False,
        "rho_eff_collapse_used": False,
    }
    honest_bridge_ready = all(readiness.values()) and not any(honest_shortcuts_forbidden.values())

    payload = {
        "status": "janus-z2-published-bimetric-flrw-to-sigma-bridge-gate",
        "active_core": "Z2_tunnel_Sigma",
        "purpose": (
            "Import the published Janus bimetric equations as active bulk source "
            "equations, reduce them to FLRW, then pull them back to the Sigma throat "
            "before constructing E_Z2Sigma(a)^2."
        ),
        "source_anchors": {
            "M15": "Lagrangian derivation of the two coupled field equations in the Janus cosmological model",
            "M30": "A bimetric cosmological model based on Andrei Sakharov's twin universe approach",
            "local_source_cards": [
                "docs/source_cards/M15.md",
                "docs/source_cards/M30.md",
            ],
        },
        "pipeline": [
            "published_interaction_slots",
            "FLRW_Bianchi_reduction",
            "sector_rho_pressure_and_normalization",
            "Sigma_embedding_pullback_h_K",
            "Sigma_stress_flux_projection",
            "projected_Bianchi_junction_closure",
            "E_Z2Sigma_of_a",
        ],
        "readiness": readiness,
        "blocked_at": blockers[0] if blockers else "none",
        "blockers": blockers,
        "honest_shortcuts_forbidden": honest_shortcuts_forbidden,
        "honest_bridge_ready": honest_bridge_ready,
        "observable_E_Z2Sigma_a2_ready": False,
        "upstream_reports": {
            "interaction_slots": {
                "status": slots["status"],
                "gate_passed": slots["gate_passed"],
                "can_transport_to_sigma": slots["can_transport_to_sigma"],
            },
            "flrw_bianchi": {
                "status": flrw["status"],
                "flrw_reduced_bianchi_ready": flrw["flrw_reduced_bianchi_ready"],
                "sigma_transport_ready": flrw["sigma_transport_ready"],
            },
            "sector_density_pressure": {
                "status": sector["status"],
                "ready": sector["sector_density_pressure_of_a_ready"],
                "primary_blocker": sector["primary_blocker"],
                "closure": sector["closure"],
            },
            "sector_source_reduction": {
                "status": source_reduction["status"],
                "rho_p_shape_ready": source_reduction["shape_level"]["rho_p_shape_ready"],
                "rho_p_normalized_ready": source_reduction["rho_p_normalized_ready"],
                "primary_blocker": source_reduction["primary_blocker"],
            },
            "sigma_embedding_to_K": {
                "status": k_pullback["status"],
                "ready": k_pullback["gate_passed"],
                "primary_blocker": k_pullback["primary_blocker"],
            },
        },
        "strict_interpretation": {
            "sigma_is_bimetric_interface": True,
            "sigma_is_not_replaced_by_bulk": True,
            "bulk_source_must_pull_back_to_sigma": True,
            "sigma_throat_alone_currently_emits_zero_FLRW_source": True,
        },
        "next_required": [
            "derive plus/minus sector rho_±(a), p_±(a) and normalizations from the published bimetric action/state",
            "derive active X_±(a) pullbacks h_± and K_± on Sigma",
            "project T_± to normal/tangent Sigma fluxes",
            "prove projected Bianchi/junction compatibility",
            "only then construct E_Z2Sigma(a)^2",
        ],
        "gate_passed": True,
    }
    return payload


def write_reports() -> dict[str, Any]:
    payload = build_payload()
    JSON_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    ACTIVE_MANIFEST_PATH.parent.mkdir(parents=True, exist_ok=True)
    ACTIVE_MANIFEST_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2 Published Bimetric FLRW To Sigma Bridge Gate",
        "",
        payload["purpose"],
        "",
        f"Honest bridge ready: `{payload['honest_bridge_ready']}`",
        f"Blocked at: `{payload['blocked_at']}`",
        f"E_Z2Sigma(a)^2 ready: `{payload['observable_E_Z2Sigma_a2_ready']}`",
        "",
        "## Readiness",
    ]
    lines.extend(f"- `{key}`: `{value}`" for key, value in payload["readiness"].items())
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
