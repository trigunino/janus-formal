from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.derive_p0_eft_janus_z2_sigma_m30_bulk_to_sigma_distribution_reduction import (
    build_payload as build_bulk_to_sigma_reduction,
)
from scripts.derive_p0_eft_janus_z2_sigma_m30_z2_symmetric_force_cancellation import (
    build_payload as build_z2_force_cancellation,
)


REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_scross_m30_boundary_reduction_audit_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_scross_m30_boundary_reduction_audit_gate.json"
)
M15_TEXT = Path(
    "data/raw/janus_library_text/"
    "M15_lagrangian-derivation-of-the-two-coupled-field-equations-in-the-janus-cosmologic.txt"
)
M30_TEXT = Path(
    "data/raw/janus_library_text/"
    "M30_a-bimetric-cosmological-model-based-on-andrei-sakharov-s-twin-universe-approach.txt"
)


def _found(path: Path, phrase: str) -> bool:
    if not path.exists():
        return False
    return phrase.lower() in path.read_text(encoding="utf-8", errors="ignore").lower()


def build_payload() -> dict:
    bulk_to_sigma = build_bulk_to_sigma_reduction()
    z2_cancellation = build_z2_force_cancellation()
    janus_evidence = {
        "m15_text_available": M15_TEXT.exists(),
        "m30_text_available": M30_TEXT.exists(),
        "m15_bivariation_found": _found(M15_TEXT, "bivariation"),
        "m15_delta_g_constraint_found": _found(M15_TEXT, "delta g")
        or _found(M15_TEXT, "deltag")
        or _found(M15_TEXT, "δg(+)"),
        "m30_two_layer_action_found": _found(M30_TEXT, "two-layer action"),
        "m30_interaction_tensors_found": _found(M30_TEXT, "interaction tensors"),
        "m30_bianchi_found": _found(M30_TEXT, "Bianchi"),
    }
    external_bibliography = [
        {
            "id": "brown-york-1992",
            "url": "https://arxiv.org/abs/gr-qc/9209012",
            "supports": "boundary stress from action variation",
            "provides_janus_sigma_reduction": False,
        },
        {
            "id": "israel-junction-conditions",
            "url": "https://doi.org/10.1007/BF02710419",
            "supports": "thin-shell jump conditions",
            "provides_janus_sigma_reduction": False,
        },
        {
            "id": "einstein-cartan-thin-shell",
            "url": "https://arxiv.org/abs/2006.04044",
            "supports": "torsion-compatible shell junction structure",
            "provides_janus_sigma_reduction": False,
        },
        {
            "id": "janus-m30",
            "url": "https://arxiv.org/pdf/2412.04644v3",
            "supports": "two-layer Janus action and interaction tensors",
            "provides_janus_sigma_reduction": False,
        },
    ]
    closure = {
        "janus_two_layer_action_source_available": bool(
            janus_evidence["m30_two_layer_action_found"]
            and janus_evidence["m30_interaction_tensors_found"]
        ),
        "janus_bivariation_source_available": bool(
            janus_evidence["m15_bivariation_found"]
            and janus_evidence["m15_delta_g_constraint_found"]
        ),
        "generic_boundary_variation_bibliography_available": True,
        "generic_junction_bibliography_available": True,
        "explicit_S_Sbar_to_Sigma_pullback_found": False,
        "explicit_Sigma_support_or_delta_distribution_found": False,
        "explicit_phi_L_transport_from_M30_found": False,
        "explicit_counterterm_density_from_M30_found": False,
        "conditional_bulk_to_sigma_force_formula_derived": bool(
            bulk_to_sigma["derived"]["normal_variation_formula_derived"]
        ),
        "strict_Z2_bulk_force_cancels": bool(
            z2_cancellation["formulae"]["force_after_Z2"] == "F_Sigma = 0"
        ),
        "can_reduce_M30_interaction_terms_to_Sigma_counterterm": False,
    }
    blockers = [
        key
        for key in [
            "explicit_S_Sbar_to_Sigma_pullback_found",
            "explicit_Sigma_support_or_delta_distribution_found",
            "explicit_phi_L_transport_from_M30_found",
            "explicit_counterterm_density_from_M30_found",
        ]
        if not closure[key]
    ]
    return {
        "status": "janus-z2-sigma-scross-m30-boundary-reduction-audit",
        "route_status": "janus-action-found-sigma-reduction-not-found",
        "janus_evidence": janus_evidence,
        "external_bibliography": external_bibliography,
        "closure": closure,
        "bulk_to_sigma_reduction": {
            "status": bulk_to_sigma["status"],
            "derivation_kind": bulk_to_sigma["derivation_kind"],
            "conditional_force_formula_derived": bulk_to_sigma["derived"][
                "normal_variation_formula_derived"
            ],
            "explicit_counterterm_density_derived": bulk_to_sigma["derived"][
                "explicit_counterterm_density_derived"
            ],
            "primary_blocker": bulk_to_sigma["primary_blocker"],
        },
        "strict_Z2_force_cancellation": {
            "status": z2_cancellation["status"],
            "bulk_M30_generates_counterterm": z2_cancellation["consequences"][
                "bulk_M30_interaction_generates_sigma_counterterm_under_strict_Z2"
            ],
            "E_counterterm_from_bulk_M30": z2_cancellation["consequences"][
                "E_counterterm_from_bulk_M30_under_strict_Z2"
            ],
            "need_tunnel_defect_for_nonzero_counterterm": z2_cancellation[
                "consequences"
            ]["need_independent_tunnel_defect_action_for_nonzero_E_counterterm"],
        },
        "gate_passed": bool(closure["can_reduce_M30_interaction_terms_to_Sigma_counterterm"]),
        "primary_blocker": "none" if not blockers else blockers[0],
        "blockers": blockers,
        "next_required": [
            "choose strict Z2 transparency or derive an independent tunnel-defect action",
            "if strict Z2: route M30 bulk channel to zero Sigma force, not to L_ct",
            "if defect: derive its local Sigma density and phi/L or embedding variation law",
            "only then feed counterterm residual tensors R_h_ab, R_K_ab, and R_chi",
        ],
        "verdict": (
            "M15/M30 restore the accepted Janus bivariational/two-layer action context, "
            "and standard boundary literature supplies generic variational machinery. "
            "A normal-variation reduction gives a conditional Sigma force formula, "
            "but strict Z2 descent cancels the bulk M30 force on Sigma. A nonzero "
            "counterterm must therefore come from an independent tunnel-defect action, "
            "not from M30 bulk interaction terms alone."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# Janus Z2/Sigma M30 Boundary Reduction Audit Gate",
        "",
        f"Route status: `{payload['route_status']}`",
        f"Gate passed: `{payload['gate_passed']}`",
        f"Primary blocker: `{payload['primary_blocker']}`",
        "",
        payload["verdict"],
        "",
        "## Closure",
    ]
    lines.extend(f"- `{key}`: `{value}`" for key, value in payload["closure"].items())
    lines.extend(["", "## Bulk-to-Sigma Reduction"])
    lines.extend(
        f"- `{key}`: `{value}`"
        for key, value in payload["bulk_to_sigma_reduction"].items()
    )
    lines.extend(["", "## Strict Z2 Force Cancellation"])
    lines.extend(
        f"- `{key}`: `{value}`"
        for key, value in payload["strict_Z2_force_cancellation"].items()
    )
    lines.extend(["", "## External Bibliography"])
    lines.extend(
        f"- `{row['id']}`: {row['url']} ({row['supports']})"
        for row in payload["external_bibliography"]
    )
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
