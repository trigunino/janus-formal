from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_tunnel_embedding_constraint_count_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_tunnel_embedding_constraint_count_gate.json")


def build_payload() -> dict:
    declared = {
        "active_embedding_problem_declared": True,
        "embedding_unknown_functions_declared": True,
        "induced_metric_matching_constraints_declared": True,
        "Z2_equivariance_constraints_declared": True,
        "regular_throat_constraint_declared": True,
        "throat_radius_law_gate_declared": True,
        "throat_radius_variational_equation_gate_declared": True,
        "throat_radius_variational_equation_ready": True,
        "throat_radius_block_expansion_gate_declared": True,
        "throat_radius_block_ledger_declared": True,
        "embedding_gauge_policy_gate_declared": True,
        "embedding_gauge_policy_declared": True,
        "embedding_gauge_equation_gate_declared": True,
        "embedding_gauge_equations_ready": True,
    }
    closure = {
        "independent_constraint_count_sufficient": False,
        "throat_radius_law_derived": False,
        "embedding_gauge_fixed": False,
        "X_plus_minus_of_a_determined": False,
    }
    unknowns = [
        "T_plus(a)",
        "R_plus(a)",
        "T_minus(a)",
        "R_minus(a)",
        "R_Sigma(a)",
    ]
    constraints = [
        "pullback(g_plus)=h_Sigma(a)",
        "pullback(g_minus)=h_Sigma(a)",
        "Z2 equivariance between X_plus and X_minus",
        "regular nonzero throat radius",
    ]
    return {
        "status": "janus-z2-sigma-tunnel-embedding-constraint-count-gate",
        "active_core": "Z2_tunnel_Sigma",
        "bibliography_checked": True,
        "bibliography_result": (
            "Janus topology plus thin-shell embedding machinery declare the problem, "
            "but no primary source fixes the resolved throat radius law R_Sigma(a)."
        ),
        "declared": declared,
        "closure": closure,
        "unknown_functions": unknowns,
        "known_constraints": constraints,
        "unknown_function_count": len(unknowns),
        "declared_constraint_count": len(constraints),
        "embedding_constraint_ledger_declared": all(declared.values()),
        "embedding_constraint_closure_ready": all(declared.values()) and all(closure.values()),
        "missing_to_close": [
            "pass_throat_radius_law_gate",
            "solve_throat_radius_variational_equation_for_R_Sigma_of_a",
            "reduce_all_throat_radius_radial_blocks",
            "pass_embedding_gauge_policy_gate",
            "insert_throat_radius_law_into_embedding_gauge_equations",
            "prove_constraints_determine_X_plus_minus_of_a",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Tunnel Embedding Constraint Count Gate",
        "",
        f"Active core: `{payload['active_core']}`",
        f"Ledger declared: `{payload['embedding_constraint_ledger_declared']}`",
        f"Closure ready: `{payload['embedding_constraint_closure_ready']}`",
        f"Unknown functions: `{payload['unknown_function_count']}`",
        f"Declared constraints: `{payload['declared_constraint_count']}`",
        "",
        "## Missing To Close",
    ]
    lines.extend(f"- `{item}`" for item in payload["missing_to_close"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
