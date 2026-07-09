from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_sigma_boundary_action_support_gate import (
    build_payload as build_sigma_boundary_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_counterterm_boundary_action_functional_gate import (
    build_payload as build_counterterm_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_plus_minus_dirac_matter_action_gate import (
    build_payload as build_matter_action_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_transport_map_derivation_gate import (
    build_payload as build_transport_map_payload,
)
from scripts.build_p0_janus_active_cross_action_acceptance_gate import (
    build_payload as build_cross_action_payload,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_active_first_action_assembly_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_active_first_action_assembly_gate.json")


def build_payload(*, embedding_manifest_path: Path | None = None) -> dict:
    sigma = build_sigma_boundary_payload()
    if embedding_manifest_path is None:
        matter = build_matter_action_payload()
    else:
        matter = build_matter_action_payload(embedding_manifest_path=embedding_manifest_path)
    counterterm = build_counterterm_payload()
    transport = build_transport_map_payload()
    cross = build_cross_action_payload()
    terms = {
        "S_grav_plus": "bulk first-order gravity on M_plus with active Z2/Sigma fields",
        "S_grav_minus": "bulk first-order gravity on M_minus with active Z2/Sigma fields",
        "S_Sigma": "Sigma-localized boundary/junction action",
        "S_matter_plus": "plus matter action from active plus spinor/tetrad data",
        "S_matter_minus": "minus matter action from active minus spinor/tetrad data",
        "S_ct": "Sigma counterterm local density action",
        "S_cross_transport": "source-derived same-bridge transport/cross action for M_-+ and M_+-",
    }
    closure = {
        "z4_CMB_non_evidence_policy_imported": True,
        "Z4_action_reuse_forbidden": True,
        "active_core_is_Z2_tunnel_Sigma": True,
        "sigma_boundary_action_imported": True,
        "plus_minus_matter_action_imported": True,
        "counterterm_boundary_action_imported": True,
        "transport_map_derivation_imported": True,
        "same_sector_stress_conservation_imported": True,
        "bulk_gravity_plus_declared": True,
        "bulk_gravity_minus_declared": True,
        "sigma_boundary_term_declared": True,
        "plus_matter_term_declared": True,
        "minus_matter_term_declared": True,
        "counterterm_term_declared": True,
        "transport_cross_term_declared": True,
        "no_observational_fit": True,
        "active_first_action_skeleton_written": True,
        "sigma_boundary_action_closed": bool(sigma["full_boundary_action_closed_on_sigma"]),
        "plus_matter_action_ready": bool(matter["closure"]["plus_matter_action_ready"]),
        "minus_matter_action_ready": bool(matter["closure"]["minus_matter_action_ready"]),
        "counterterm_boundary_action_closed": bool(
            counterterm["boundary_action_functional_closed"]
        ),
        "transport_bridge_declared": bool(transport["declared_transport_layer_ready"]),
        "cross_action_source_accepted": bool(cross["active_cross_action_source_accepted"]),
        "cross_action_new_axiom_not_adopted": not bool(cross["new_axiom_adopted"]),
        "active_first_action_assembled": False,
    }
    declared_ready = all(
        closure[key]
        for key in [
            "z4_CMB_non_evidence_policy_imported",
            "Z4_action_reuse_forbidden",
            "active_core_is_Z2_tunnel_Sigma",
            "sigma_boundary_action_imported",
            "plus_minus_matter_action_imported",
            "counterterm_boundary_action_imported",
            "transport_map_derivation_imported",
            "same_sector_stress_conservation_imported",
            "bulk_gravity_plus_declared",
            "bulk_gravity_minus_declared",
            "sigma_boundary_term_declared",
            "plus_matter_term_declared",
            "minus_matter_term_declared",
            "counterterm_term_declared",
            "transport_cross_term_declared",
            "no_observational_fit",
            "active_first_action_skeleton_written",
        ]
    )
    source_ready = all(closure.values())
    blockers = [key for key, value in closure.items() if not value]
    primary_blocker = "none"
    if not source_ready:
        primary_blocker = blockers[0]
        if not matter["plus_minus_dirac_matter_action_ready"]:
            primary_blocker = matter["primary_blocker"]
    return {
        "status": "janus-z2-sigma-active-first-action-assembly-gate",
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_Z2Sigma_first_action",
        "action_formula": (
            "S_active = S_grav_plus + S_grav_minus + S_Sigma + "
            "S_matter_plus + S_matter_minus + S_ct + S_cross_transport"
        ),
        "terms": terms,
        "closure": closure,
        "declared_action_layer_ready": declared_ready,
        "source_derivation_ready": source_ready,
        "gate_passed": declared_ready and source_ready,
        "primary_blocker": primary_blocker,
        "blockers": blockers,
        "upstream": {
            "sigma_boundary": {
                "gate": sigma["status"],
                "closed": sigma["full_boundary_action_closed_on_sigma"],
            },
            "matter_action": {
                "gate": matter["status"],
                "ready": matter["plus_minus_dirac_matter_action_ready"],
                "primary_blockers": [
                    key for key, value in matter["closure"].items() if not value
                ],
            },
            "counterterm": {
                "gate": counterterm["status"],
                "boundary_action_functional_closed": counterterm[
                    "boundary_action_functional_closed"
                ],
                "density_inputs_allowed": counterterm[
                    "counterterm_local_density_action_inputs_allowed"
                ],
            },
            "transport": {
                "gate": transport["status"],
                "declared": transport["declared_transport_layer_ready"],
                "source_ready": transport["source_derivation_ready"],
            },
            "cross_action": {
                "gate": cross["status"],
                "source_accepted": cross["active_cross_action_source_accepted"],
                "can_adopt_as_new_axiom": cross["can_adopt_as_explicit_new_axiom"],
                "new_axiom_adopted": cross["new_axiom_adopted"],
            },
        },
        "z4_policy": {
            "Z4_archive_reference_allowed": True,
            "Z4_action_reuse_used": False,
            "Z4_can_close_active_action": False,
        },
        "next_required": [
            "source_accept_or_reject_S_cross_transport_without_Z4_reuse",
            "derive_cross_transport_variation_for_M_minus_to_plus_and_M_plus_to_minus",
            "expand_counterterm_coefficients_if_density_inputs_are_needed",
            "then_mark_active_first_action_assembled",
        ],
        "interpretation": (
            "The active first action is now a named Z2/Sigma assembly target. Z4 is "
            "diagnostic only; it cannot close this gate. The current blockers are "
            "the counterterm closure and a source-accepted cross/transport action."
        ),
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Active First Action Assembly Gate",
        "",
        f"Formula: `{payload['action_formula']}`",
        f"Gate passed: `{payload['gate_passed']}`",
        f"Primary blocker: `{payload['primary_blocker']}`",
        "",
        payload["interpretation"],
        "",
        "## Terms",
    ]
    lines.extend(f"- `{key}`: `{value}`" for key, value in payload["terms"].items())
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
