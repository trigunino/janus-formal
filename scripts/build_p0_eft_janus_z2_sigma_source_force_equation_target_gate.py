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
from scripts.derive_p0_eft_janus_z2_sigma_brane_normal_force_residual import (
    build_payload as build_brane_residual,
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
    brane_residual = build_brane_residual()
    phi_l_ready = bool(phi_l["phi_l_variation_law_ready"])
    embedding_ready = bool(embedding["readiness"]["active_embedding_ready"])
    brane_normal_ready = bool(brane_residual["strict_Z2_closes_normal_force"])
    source_route_available = phi_l_ready or embedding_ready or brane_normal_ready
    source_force_derived = False
    brane_bibliography = [
        {
            "id": "battye-carter-2001",
            "url": "https://arxiv.org/abs/hep-th/0101061",
            "role": "codimension-one brane requires a Newton-second-law-like dynamical condition in addition to Darmois-Israel",
            "janus_use": "Z2-enforced branch can make the normal force condition trivial; non-Z2 residual must be derived, not fitted",
        },
        {
            "id": "carter-2000",
            "url": "https://arxiv.org/abs/gr-qc/0012036",
            "role": "surface stress contracted with second fundamental tensor equals orthogonal external force",
            "janus_use": "source-force target formula for Sigma",
        },
        {
            "id": "capovilla-guven-1995",
            "url": "https://arxiv.org/abs/gr-qc/9411060",
            "role": "normal deformations of membrane actions built from local worldsheet scalars",
            "janus_use": "variation toolkit for local tunnel-defect action only if a defect is forced",
        },
        {
            "id": "mars-senovilla-2002",
            "url": "https://arxiv.org/abs/gr-qc/0201054",
            "role": "general hypersurface geometry, junction conditions, and distributional Bianchi identities",
            "janus_use": "Bianchi/distribution guard for active Sigma junction",
        },
        {
            "id": "brill-hayward-1994",
            "url": "https://arxiv.org/abs/gr-qc/9403018",
            "role": "action changes under topological boundary identifications",
            "janus_use": "possible corner/gluing correction audit; not a free counterterm source",
        },
    ]
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
        "brane_newton_second_law_bibliography_found": True,
        "normal_force_formula_target_refined": True,
        "brane_normal_force_residual_symbolic_ready": bool(
            brane_residual["residual_symbolic_ready"]
        ),
        "brane_normal_force_residual_values_ready": bool(
            brane_residual["residual_values_ready"]
        ),
        "brane_normal_force_equation_closed_by_strict_Z2": brane_normal_ready,
        "strict_Z2_condition_may_trivialize_force": True,
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
            "brane_normal_dynamics": (
                "barT^{ab}_Sigma K_ab^rho = f_perp^rho; strict Z2 may set f_perp=0, "
                "otherwise residual must come from active embedding/junction stress"
            ),
        },
        "brane_bibliography": brane_bibliography,
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
            "brane_normal_force_residual": {
                "gate": brane_residual["status"],
                "symbolic_ready": brane_residual["residual_symbolic_ready"],
                "values_ready": brane_residual["residual_values_ready"],
                "primary_blocker": brane_residual["primary_blocker"],
            },
        },
        "forbidden_shortcuts": [
            "same-sector geodesics alone do not derive receiver-force equations",
            "Lorentz admissibility of L does not imply C.K cancellation",
            "Q_cross cannot absorb force residuals",
        ],
        "next_required": [
            "instantiate Carter/Battye normal brane equation on active Sigma",
            "insert active S_ab and K_ab from the Z2 tunnel junction",
            "test whether strict Z2 makes f_perp vanish or leaves a forced residual",
            "derive plus force equation from phi/L variation or embedding equation",
            "derive minus force equation from mirror variation or embedding equation",
            "feed sourceForceEquationsDerived into connection-force residual matching",
        ],
        "interpretation": (
            "The source-force equations are now refined to the standard brane normal "
            "dynamics target. The gate does not close them from geodesics, Lorentz "
            "admissibility, or Q_cross."
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
    lines.extend(["", "## Brane Dynamics Bibliography"])
    lines.extend(
        f"- `{row['id']}`: {row['url']} ({row['janus_use']})"
        for row in payload["brane_bibliography"]
    )
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
