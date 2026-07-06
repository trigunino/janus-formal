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
from scripts.build_p0_eft_janus_z2_sigma_connection_force_residual_matching_gate import (
    build_payload as build_connection_matching,
)
from scripts.build_p0_eft_janus_z2_sigma_scross_phi_l_variation_law_gate import (
    build_payload as build_phi_l,
)


REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_source_force_equation_target_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_source_force_equation_target_gate.json"
)


def build_payload(*, embedding_manifest_path: Path | None = None) -> dict:
    if embedding_manifest_path is None:
        embedding = build_embedding()
        matching = build_connection_matching()
    else:
        embedding = build_embedding(embedding_manifest_path=embedding_manifest_path)
        matching = build_connection_matching(embedding_manifest_path=embedding_manifest_path)
    phi_l = build_phi_l()
    phi_l_ready = bool(phi_l["phi_l_variation_law_ready"])
    embedding_ready = bool(embedding["readiness"]["active_embedding_ready"])
    source_route_available = phi_l_ready or embedding_ready
    source_force_derived = False
    closure = {
        "connection_force_residual_matching_gate_imported": True,
        "S_cross_phi_L_variation_law_gate_imported": True,
        "active_embedding_readiness_gate_imported": True,
        "plus_force_equation_target_written": True,
        "minus_force_equation_target_written": True,
        "phi_L_source_route_allowed": True,
        "active_embedding_source_route_allowed": True,
        "no_geodesic_shortcut": True,
        "no_Lorentz_admissibility_shortcut": True,
        "no_Qcross_force_absorption": True,
        "phi_L_variation_law_ready": phi_l_ready,
        "active_embedding_ready": embedding_ready,
        "source_route_available": source_route_available,
        "plus_source_force_equation_derived": source_force_derived,
        "minus_source_force_equation_derived": source_force_derived,
        "source_force_equations_derived": source_force_derived,
        "feeds_connection_force_residual_matching": source_force_derived,
    }
    target_keys = [
        "connection_force_residual_matching_gate_imported",
        "S_cross_phi_L_variation_law_gate_imported",
        "active_embedding_readiness_gate_imported",
        "plus_force_equation_target_written",
        "minus_force_equation_target_written",
        "phi_L_source_route_allowed",
        "active_embedding_source_route_allowed",
        "no_geodesic_shortcut",
        "no_Lorentz_admissibility_shortcut",
        "no_Qcross_force_absorption",
    ]
    ready_keys = [
        "source_route_available",
        "plus_source_force_equation_derived",
        "minus_source_force_equation_derived",
        "source_force_equations_derived",
        "feeds_connection_force_residual_matching",
    ]
    target_ready = all(closure[key] for key in target_keys)
    source_ready = target_ready and all(closure[key] for key in ready_keys)
    blockers = [key for key in ready_keys if not closure[key]]
    return {
        "status": "janus-z2-sigma-source-force-equation-target-gate",
        "route_status": (
            "source_force_equations_ready"
            if source_ready
            else "target_written_waiting_for_source_force_derivation"
        ),
        "force_targets": {
            "plus": (
                "E_phi/E_L or embedding equation => plus receiver-force equation "
                "cancelling +B_plus C.K residual"
            ),
            "minus": (
                "mirror E_phi/E_L or embedding equation => minus receiver-force equation "
                "cancelling -B_minus C.K residual"
            ),
        },
        "closure": closure,
        "target_ready": target_ready,
        "source_force_ready": source_ready,
        "gate_passed": source_ready,
        "primary_blocker": "none" if source_ready else blockers[0],
        "blockers": blockers,
        "upstream": {
            "phi_L": {
                "gate": phi_l["status"],
                "ready": phi_l_ready,
                "primary_blocker": phi_l["primary_blocker"],
            },
            "embedding": {
                "gate": embedding["status"],
                "ready": embedding_ready,
                "primary_blocker": embedding["primary_blocker"],
            },
            "connection_matching": {
                "gate": matching["status"],
                "matching_ready": matching["matching_ready"],
                "primary_blocker": matching["primary_blocker"],
            },
        },
        "forbidden_shortcuts": [
            "same-sector geodesics alone do not derive receiver-force equations",
            "Lorentz admissibility of L does not imply C.K cancellation",
            "Q_cross cannot absorb force residuals",
        ],
        "next_required": [
            "derive plus force equation from phi/L variation or embedding equation",
            "derive minus force equation from mirror variation or embedding equation",
            "feed sourceForceEquationsDerived into connection-force residual matching",
        ],
        "interpretation": (
            "The source-force equations are now the explicit next target. The gate "
            "does not close them from geodesics, Lorentz admissibility, or Q_cross."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# Janus Z2/Sigma Source Force Equation Target Gate",
        "",
        f"Route status: `{payload['route_status']}`",
        f"Gate passed: `{payload['gate_passed']}`",
        f"Primary blocker: `{payload['primary_blocker']}`",
        "",
        payload["interpretation"],
        "",
        "## Force Targets",
    ]
    lines.extend(f"- `{key}`: `{value}`" for key, value in payload["force_targets"].items())
    lines.extend(["", "## Forbidden Shortcuts"])
    lines.extend(f"- `{item}`" for item in payload["forbidden_shortcuts"])
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
