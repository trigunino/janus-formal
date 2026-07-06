from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z2_sigma_active_embedding_readiness_gate import (
    build_payload as build_embedding,
)
from scripts.build_p0_eft_janus_z2_sigma_scross_transport_source_acceptance_gate import (
    build_payload as build_scross,
)
from scripts.build_p0_eft_janus_z2_sigma_source_force_equation_target_gate import (
    build_payload as build_source_force,
)


REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_force_source_route_decision_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_force_source_route_decision_gate.json"
)


def _score(blockers: list[str]) -> int:
    return len(blockers)


def build_payload() -> dict:
    source_force = build_source_force()
    scross = build_scross()
    embedding = build_embedding()
    phi_l_blockers = [
        "independent_S_cross_functional_found",
        "phi_L_variation_law_found",
        "source_accepted_as_published_Janus",
    ]
    embedding_blockers = [
        "R_Sigma_solution_certificate",
    ]
    route_scores = {
        "phi_L_route": _score(phi_l_blockers),
        "embedding_route": _score(embedding_blockers),
    }
    preferred = "embedding_route"
    closure = {
        "source_force_equation_target_gate_imported": True,
        "S_cross_transport_source_acceptance_gate_imported": True,
        "active_embedding_readiness_gate_imported": True,
        "phi_L_route_declared": True,
        "embedding_route_declared": True,
        "phi_L_hard_blocker_identified": not scross["source_acceptance_ready"],
        "embedding_hard_blocker_identified": not embedding["readiness"]["active_embedding_ready"],
        "no_route_closed_prematurely": not source_force["source_force_ready"],
        "no_auxiliary_route_archived": True,
        "embedding_route_preferred_for_next_attack": preferred == "embedding_route",
        "phi_L_route_kept_as_auxiliary": True,
        "main_branch_next_blocker_updated": True,
    }
    return {
        "status": "janus-z2-sigma-force-source-route-decision-gate",
        "route_status": "embedding_route_preferred_phi_l_kept_auxiliary",
        "routes": {
            "phi_L_route": {
                "purpose": "derive source force equations from S_cross phi/L variation",
                "hard_blockers": phi_l_blockers,
                "score": route_scores["phi_L_route"],
                "status": "auxiliary_open",
            },
            "embedding_route": {
                "purpose": "derive source force equations from active embedding equations",
                "hard_blockers": embedding_blockers,
                "score": route_scores["embedding_route"],
                "status": "preferred_next_attack",
            },
        },
        "closure": closure,
        "gate_passed": all(closure.values()),
        "preferred_next_attack": preferred,
        "main_branch_next_blocker": "R_Sigma_solution_certificate",
        "auxiliary_route": "phi_L_route",
        "upstream": {
            "source_force": {
                "gate": source_force["status"],
                "ready": source_force["source_force_ready"],
                "primary_blocker": source_force["primary_blocker"],
            },
            "S_cross": {
                "gate": scross["status"],
                "ready": scross["source_acceptance_ready"],
                "primary_blocker": scross["primary_blocker"],
            },
            "embedding": {
                "gate": embedding["status"],
                "ready": embedding["readiness"]["active_embedding_ready"],
                "primary_blocker": embedding["primary_blocker"],
            },
        },
        "next_required": [
            "attack R_Sigma_solution_certificate first",
            "use active embedding to unlock pullback volumes, determinant-gradient split, and force-source route",
            "keep phi/L S_cross route as auxiliary until independent S_cross appears",
        ],
        "interpretation": (
            "Both routes remain open, but the embedding route has the smaller explicit "
            "hard-blocker set. The next main-branch attack should be R_Sigma_solution_certificate; "
            "the phi/L route stays auxiliary."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# Janus Z2/Sigma Force Source Route Decision Gate",
        "",
        f"Route status: `{payload['route_status']}`",
        f"Gate passed: `{payload['gate_passed']}`",
        f"Preferred next attack: `{payload['preferred_next_attack']}`",
        f"Main branch next blocker: `{payload['main_branch_next_blocker']}`",
        "",
        payload["interpretation"],
        "",
        "## Routes",
    ]
    for name, route in payload["routes"].items():
        lines.append(f"- `{name}`: `{route['status']}`, score `{route['score']}`")
        lines.append(f"  - purpose: `{route['purpose']}`")
        lines.append(f"  - blockers: `{', '.join(route['hard_blockers'])}`")
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    return "\n".join(lines)


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(render_markdown(payload), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
