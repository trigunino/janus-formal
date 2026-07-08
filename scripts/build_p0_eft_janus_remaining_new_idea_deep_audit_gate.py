from __future__ import annotations

import json
from pathlib import Path
from typing import Any


REPORTS = Path("outputs/reports")
JSON_PATH = REPORTS / "p0_eft_janus_remaining_new_idea_deep_audit_gate.json"
REPORT_PATH = REPORTS / "p0_eft_janus_remaining_new_idea_deep_audit_gate.md"


ROUTES: list[dict[str, Any]] = [
    {
        "id": "epp_rqf_quasilocal_energy",
        "what_can_be_done": "replace naive Brown-York by nonstationary FRW-compatible observer quasilocal energy",
        "deep_test": "does a boundary observer energy produce H0_Z2Sigma without new source?",
        "result": "methodological_upgrade_only",
        "why_not_alpha": "needs active observer congruence, reference embedding, and time generator for Janus/PT",
        "next_if_kept": "derive active RQF data on the Janus throat",
        "closes_alpha_now": False,
    },
    {
        "id": "topological_casimir_compact_state",
        "what_can_be_done": "compute vacuum energy from compact topology once fields and boundary conditions are fixed",
        "deep_test": "can topology alone give a unique rho_vac?",
        "result": "not_from_topology_alone",
        "why_not_alpha": "requires field content, spectrum, renormalization prescription, and absolute radius",
        "next_if_kept": "derive spectrum of Janus fields on resolved S4/RP4/Sigma",
        "closes_alpha_now": False,
    },
    {
        "id": "minisuperspace_quantization",
        "what_can_be_done": "quantize the exact Janus background orbit and look for alpha eigenvalues",
        "deep_test": "does the current published exact solution define a finite self-adjoint quantum problem?",
        "result": "formal_target_only",
        "why_not_alpha": "missing finite action, canonical variable, measure, self-adjoint domain, and boundary condition",
        "next_if_kept": "materialize Janus bimetric minisuperspace action",
        "closes_alpha_now": False,
    },
    {
        "id": "flux_quantized_four_form_or_tqft",
        "what_can_be_done": "make alpha discrete through compact flux or TQFT level",
        "deep_test": "does Janus provide gauge field, compact cycle, charge unit, and primitive sector?",
        "result": "overlaps_four_form_but_missing_Janus_origin",
        "why_not_alpha": "no Janus-derived TQFT/gauge sector or primitive flux law",
        "next_if_kept": "derive boundary TQFT from PT/Sigma action, not add it",
        "closes_alpha_now": False,
    },
    {
        "id": "asymptotic_or_internal_null_charge",
        "what_can_be_done": "define alpha as ADM/Bondi/Wald-Zoupas-like boundary mass charge",
        "deep_test": "does Janus provide an integrable null/asymptotic charge?",
        "result": "right_framework_missing_boundary_data",
        "why_not_alpha": "missing null boundary conditions, charge integrability, and generator normalization",
        "next_if_kept": "promote PT bridge to active null boundary with phase-space charge",
        "closes_alpha_now": False,
    },
]


def build_payload() -> dict[str, Any]:
    return {
        "status": "janus-remaining-new-idea-deep-audit-gate",
        "routes": ROUTES,
        "all_remaining_routes_audited": True,
        "any_remaining_route_closes_alpha_now": any(row["closes_alpha_now"] for row in ROUTES),
        "best_survivors_after_deep_audit": [
            "lightlike_brane_bridge_source",
            "unimodular_four_form_sector_constant",
            "cpt_pt_symmetric_state_law",
        ],
        "secondary_survivors": [
            "epp_rqf_quasilocal_energy",
            "minisuperspace_quantization",
            "asymptotic_or_internal_null_charge",
        ],
        "archive_as_low_priority_for_now": [
            "topological_casimir_compact_state",
            "flux_quantized_four_form_or_tqft",
        ],
        "final_deep_audit_verdict": (
            "The remaining routes do not close alpha now. They either require active Janus "
            "boundary data, active field spectrum, or a full bimetric minisuperspace action."
        ),
        "gate_passed": True,
    }


def write_reports() -> dict[str, Any]:
    payload = build_payload()
    REPORTS.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Remaining New-Idea Deep Audit Gate",
        "",
        f"Any remaining route closes alpha now: `{payload['any_remaining_route_closes_alpha_now']}`",
        "",
        "| Route | Result | Why not alpha |",
        "|---|---|---|",
        *[
            f"| `{row['id']}` | `{row['result']}` | {row['why_not_alpha']} |"
            for row in payload["routes"]
        ],
        "",
        "## Best Survivors",
        "",
        *[f"- `{item}`" for item in payload["best_survivors_after_deep_audit"]],
        "",
        "## Verdict",
        "",
        payload["final_deep_audit_verdict"],
    ]
    REPORT_PATH.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
