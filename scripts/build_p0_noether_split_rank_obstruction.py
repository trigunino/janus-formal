from __future__ import annotations

from pathlib import Path
import json

import sympy as sp


REPORT_PATH = Path("outputs/reports/p0_noether_split_rank_obstruction.md")
JSON_PATH = Path("outputs/reports/p0_noether_split_rank_obstruction.json")


def build_payload() -> dict:
    r_plus, r_minus = sp.symbols("R_plus R_minus")
    residual = sp.Matrix([r_plus, r_minus])
    diagonal_row = sp.Matrix([[1, 1]])
    split_rows = sp.eye(2)
    contrast_rows = sp.Matrix([[1, 1], [1, -1]])
    counterexample = sp.Matrix([1, -1])

    combined_residual = sp.simplify((diagonal_row * residual)[0])
    counterexample_combined = sp.simplify((diagonal_row * counterexample)[0])
    diagonal_rank = int(diagonal_row.rank())
    diagonal_nullity = len(diagonal_row.nullspace())
    split_rank = int(split_rows.rank())
    contrast_rank = int(contrast_rows.rank())

    proof_rows = [
        {
            "step": "residual_space",
            "formula": "r = (R_plus, R_minus)^T",
            "rank": 2,
            "closed": True,
            "meaning": "two separate sector residuals need two independent scalar constraints",
        },
        {
            "step": "single_diagonal_noether_identity",
            "formula": f"N_diag r = [1 1] r = {combined_residual}",
            "rank": diagonal_rank,
            "closed": True,
            "meaning": "one diagonal diffeomorphism identity gives one combined residual",
        },
        {
            "step": "kernel_counterexample",
            "formula": "(R_plus, R_minus) = (1, -1) gives R_plus + R_minus = 0",
            "rank": diagonal_rank,
            "closed": bool(counterexample_combined == 0 and counterexample != sp.zeros(2, 1)),
            "meaning": "the combined identity can hold while both separate residuals are nonzero",
        },
        {
            "step": "independent_split_rows",
            "formula": "rank([[1,0],[0,1]]) = 2 and rank([[1,1],[1,-1]]) = 2",
            "rank": split_rank,
            "closed": bool(split_rank == 2 and contrast_rank == 2),
            "meaning": "separate zeros require an independent sector identity or source-derived split equation",
        },
    ]
    zero_rustine_rules = [
        "no observational fit may be used to choose the missing split equation",
        "no Q_det/Q_cross absorption may turn one combined residual into two residual equations",
        "no hidden axiom may be smuggled in as if it were a Noether consequence",
        "prediction_ready stays false until an independent sector identity or source-derived split equation exists",
    ]
    return {
        "description": (
            "Bounded zero-rustine P0 artifact for the rank obstruction in split Noether closure."
        ),
        "status": "single-diagonal-noether-rank-one-obstruction-proved",
        "residual_vector": str(residual),
        "diagonal_noether_matrix": str(diagonal_row),
        "combined_residual": str(combined_residual),
        "diagonal_identity_rank": diagonal_rank,
        "diagonal_identity_nullity": diagonal_nullity,
        "counterexample_residual": ["1", "-1"],
        "counterexample_combined_value": str(counterexample_combined),
        "counterexample_has_nonzero_separate_residuals": True,
        "single_identity_can_force_rplus_zero": False,
        "single_identity_can_force_rminus_zero": False,
        "single_identity_can_force_both_residuals_zero": False,
        "combined_residual_constrained": True,
        "split_rows_rank": split_rank,
        "contrast_rows_rank": contrast_rank,
        "independent_sector_identity_available": False,
        "source_derived_split_equation_available": False,
        "requires_independent_sector_identity_or_source_split": True,
        "uses_observational_fit": False,
        "uses_qdet_qcross_absorption": False,
        "uses_hidden_axiom": False,
        "bounded_artifact": True,
        "zero_rustine": True,
        "proof_rows": proof_rows,
        "zero_rustine_rules": zero_rustine_rules,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "A single diagonal diffeomorphism Noether identity has rank 1 on "
            "(R_plus, R_minus). It constrains only R_plus + R_minus, so it cannot "
            "by itself force R_plus=0 and R_minus=0. Split closure needs an "
            "independent sector identity or a source-derived split equation; fit, "
            "Q_det/Q_cross absorption, and hidden axioms are forbidden."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Noether Split Rank Obstruction",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Residual vector: `{payload['residual_vector']}`",
        f"Diagonal Noether matrix: `{payload['diagonal_noether_matrix']}`",
        f"Combined residual: `{payload['combined_residual']}`",
        f"Diagonal identity rank: {payload['diagonal_identity_rank']}",
        f"Diagonal identity nullity: {payload['diagonal_identity_nullity']}",
        f"Counterexample residual: `{payload['counterexample_residual']}`",
        f"Counterexample combined value: `{payload['counterexample_combined_value']}`",
        (
            "Counterexample has nonzero separate residuals: "
            f"{payload['counterexample_has_nonzero_separate_residuals']}"
        ),
        f"Single identity can force R_plus=0: {payload['single_identity_can_force_rplus_zero']}",
        f"Single identity can force R_minus=0: {payload['single_identity_can_force_rminus_zero']}",
        (
            "Single identity can force both residuals zero: "
            f"{payload['single_identity_can_force_both_residuals_zero']}"
        ),
        f"Combined residual constrained: {payload['combined_residual_constrained']}",
        f"Split rows rank: {payload['split_rows_rank']}",
        f"Contrast rows rank: {payload['contrast_rows_rank']}",
        (
            "Independent sector identity available: "
            f"{payload['independent_sector_identity_available']}"
        ),
        (
            "Source-derived split equation available: "
            f"{payload['source_derived_split_equation_available']}"
        ),
        (
            "Requires independent sector identity or source split: "
            f"{payload['requires_independent_sector_identity_or_source_split']}"
        ),
        f"Uses observational fit: {payload['uses_observational_fit']}",
        f"Uses Qdet/Qcross absorption: {payload['uses_qdet_qcross_absorption']}",
        f"Uses hidden axiom: {payload['uses_hidden_axiom']}",
        f"Bounded artifact: {payload['bounded_artifact']}",
        f"Zero rustine: {payload['zero_rustine']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Proof Rows",
        "",
        "| step | formula | rank | closed | meaning |",
        "|---|---|---:|---:|---|",
    ]
    for row in payload["proof_rows"]:
        lines.append(
            f"| {row['step']} | `{row['formula']}` | "
            f"{row['rank']} | {row['closed']} | {row['meaning']} |"
        )
    lines.extend(["", "## Zero-Rustine Rules", ""])
    lines.extend(f"- {item}" for item in payload["zero_rustine_rules"])
    lines.extend(["", f"Verdict: {payload['verdict']}", ""])
    return "\n".join(lines)


def write_reports(report_path: Path = REPORT_PATH, json_path: Path = JSON_PATH) -> dict:
    report_path.parent.mkdir(parents=True, exist_ok=True)
    json_path.parent.mkdir(parents=True, exist_ok=True)
    payload = build_payload()
    json_path.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    report_path.write_text(render_markdown(payload), encoding="utf-8")
    return payload


def main() -> None:
    write_reports()
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {JSON_PATH}")


if __name__ == "__main__":
    main()
