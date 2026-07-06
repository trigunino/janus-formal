from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_bianchi_connection_force_cancellation_target import (
    build_payload as build_legacy_force_target,
)
from scripts.build_bianchi_mixed_stress_residual_target import (
    build_payload as build_legacy_residual_target,
)
from scripts.build_p0_eft_janus_z2_sigma_determinant_gradient_divergence_gate import (
    build_payload as build_gradient_divergence,
)


REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_connection_force_residual_matching_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_connection_force_residual_matching_gate.json"
)


def build_payload(*, embedding_manifest_path: Path | None = None) -> dict:
    if embedding_manifest_path is None:
        gradient = build_gradient_divergence()
    else:
        gradient = build_gradient_divergence(embedding_manifest_path=embedding_manifest_path)
    force = build_legacy_force_target()
    residual = build_legacy_residual_target()
    split_ready = bool(gradient["divergence_split_ready"])
    source_force_derived = False
    closure = {
        "determinant_gradient_divergence_gate_imported": True,
        "transport_compatibility_conditional_closure_gate_imported": True,
        "connection_difference_tensor_declared": True,
        "plus_receiver_connection_force_declared": True,
        "minus_receiver_connection_force_declared": True,
        "plus_determinant_gradient_term_declared": True,
        "minus_determinant_gradient_term_declared": True,
        "same_bridge_for_connection_and_stress": True,
        "no_connection_force_drop": True,
        "no_Qcross_absorption": True,
        "determinant_gradient_split_ready": split_ready,
        "plus_residual_matching_equation_written": True,
        "minus_residual_matching_equation_written": True,
        "source_force_equations_derived": source_force_derived,
        "plus_connection_force_matched": split_ready and source_force_derived,
        "minus_connection_force_matched": split_ready and source_force_derived,
        "feeds_plus_transport_compatibility": split_ready and source_force_derived,
        "feeds_minus_transport_compatibility": split_ready and source_force_derived,
    }
    target_keys = [
        "determinant_gradient_divergence_gate_imported",
        "transport_compatibility_conditional_closure_gate_imported",
        "connection_difference_tensor_declared",
        "plus_receiver_connection_force_declared",
        "minus_receiver_connection_force_declared",
        "plus_determinant_gradient_term_declared",
        "minus_determinant_gradient_term_declared",
        "same_bridge_for_connection_and_stress",
        "no_connection_force_drop",
        "no_Qcross_absorption",
        "plus_residual_matching_equation_written",
        "minus_residual_matching_equation_written",
    ]
    ready_keys = [
        "determinant_gradient_split_ready",
        "source_force_equations_derived",
        "plus_connection_force_matched",
        "minus_connection_force_matched",
        "feeds_plus_transport_compatibility",
        "feeds_minus_transport_compatibility",
    ]
    target_ready = all(closure[key] for key in target_keys)
    matching_ready = target_ready and all(closure[key] for key in ready_keys)
    blockers = [key for key in ready_keys if not closure[key]]
    return {
        "status": "janus-z2-sigma-connection-force-residual-matching-gate",
        "route_status": (
            "connection_force_residual_matching_ready"
            if matching_ready
            else "target_written_waiting_for_source_force_equations"
        ),
        "matching_identities": {
            "connection_difference": (
                "C^a_bc := Gamma_plus^a_bc - transported(Gamma_minus)^a_bc"
            ),
            "plus_residual_target": (
                "(D_plus B_plus)K_plus + B_plus D_plus K_plus "
                "matched against +B_plus C.K force terms"
            ),
            "minus_residual_target": (
                "(D_minus B_minus)K_minus + B_minus D_minus K_minus "
                "matched against -B_minus C.K force terms"
            ),
        },
        "closure": closure,
        "target_ready": target_ready,
        "matching_ready": matching_ready,
        "gate_passed": matching_ready,
        "primary_blocker": "none" if matching_ready else blockers[0],
        "blockers": blockers,
        "upstream": {
            "determinant_gradient": {
                "gate": gradient["status"],
                "split_ready": gradient["divergence_split_ready"],
                "primary_blocker": gradient["primary_blocker"],
            },
            "legacy_force_target": {
                "status": force["status"],
                "conditions_source_derived": force["conditions_source_derived"],
                "residuals_closed": force["residuals_closed"],
            },
            "legacy_residual_target": {
                "status": residual["status"],
                "hard_missing_term": residual["hard_missing_term"],
            },
        },
        "forbidden_shortcuts": [
            "do not drop C.K connection-force terms",
            "do not hide determinant gradients inside K",
            "do not absorb the residual into Q_cross",
            "do not mark transport compatibility source-derived before force equations are derived",
        ],
        "next_required": [
            "derive source force equations from phi/L or active embedding equations",
            "match plus C.K residual with determinant-gradient split",
            "match minus C.K residual with determinant-gradient split",
            "then feed transport compatibility conditional closure",
        ],
        "interpretation": (
            "The connection-force matching target is written on the active Z2/Sigma "
            "branch. It does not close because the force equations are not yet "
            "source-derived."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# Janus Z2/Sigma Connection-Force Residual Matching Gate",
        "",
        f"Route status: `{payload['route_status']}`",
        f"Gate passed: `{payload['gate_passed']}`",
        f"Primary blocker: `{payload['primary_blocker']}`",
        "",
        payload["interpretation"],
        "",
        "## Matching Identities",
    ]
    lines.extend(
        f"- `{key}`: `{value}`" for key, value in payload["matching_identities"].items()
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
