from __future__ import annotations

from pathlib import Path
import json

import sympy as sp


REPORT_PATH = Path("outputs/reports/p0_split_noether_linear_phi_candidate.md")
JSON_PATH = Path("outputs/reports/p0_split_noether_linear_phi_candidate.json")


def build_payload() -> dict:
    c1, i_matter = sp.symbols("c1 I_matter")
    phi = c1 * i_matter
    weak_sign_normalization = sp.solve([c1 - 1], [c1], dict=True)
    candidate_rows = [
        {
            "row": "candidate",
            "formula": str(phi),
            "status": "chosen-for-test",
        },
        {
            "row": "weak_sign_normalization",
            "formula": "c1=1",
            "status": "fixes overall linear sign only",
        },
        {
            "row": "metric_variation",
            "formula": "measure trace closed; full K requires delta_g T_plus, delta_g L, and pulled T_minus response",
            "status": "measure-only-closed-full-k-open",
        },
        {
            "row": "map_variation",
            "formula": "E_phi/E_L require delta pullback(T_minus) and delta(L T_minus L^T)",
            "status": "delta_L algebra closed; phi/pullback open",
        },
        {
            "row": "split_noether_substitution",
            "formula": "R_plus/R_minus cannot be evaluated before metric/map variations are explicit",
            "status": "blocked",
        },
    ]
    return {
        "description": "First Split Noether application to the minimal linear Phi=c1 I_matter candidate.",
        "status": "linear-candidate-normalized-variation-blocked",
        "candidate_rows": candidate_rows,
        "weak_sign_normalization_solution": [dict((str(k), str(v)) for k, v in row.items()) for row in weak_sign_normalization],
        "c1_fixed_by_weak_sign": True,
        "candidate_rejected": False,
        "candidate_accepted": False,
        "imatter_tensor_contract_defined": True,
        "metric_measure_variation_available": True,
        "l_variation_algebra_closed": True,
        "lorentz_projected_e_l_closed": True,
        "variation_blocked_by_missing_tensor_definition": False,
        "variation_blocked_by_missing_variational_rules": True,
        "split_noether_residuals_evaluated": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "The linear candidate can fix only the weak-field normalization c1. It is not rejected "
            "or accepted: I_matter now has a tensor contract, but Split Noether evaluation is "
            "blocked until metric, L, and phi variation rules are explicit."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Split Noether Linear Phi Candidate",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"c1 fixed by weak sign: {payload['c1_fixed_by_weak_sign']}",
        f"Candidate rejected: {payload['candidate_rejected']}",
        f"Candidate accepted: {payload['candidate_accepted']}",
        f"I_matter tensor contract defined: {payload['imatter_tensor_contract_defined']}",
        f"Metric measure variation available: {payload['metric_measure_variation_available']}",
        f"L variation algebra closed: {payload['l_variation_algebra_closed']}",
        f"Lorentz projected E_L closed: {payload['lorentz_projected_e_l_closed']}",
        f"Variation blocked by missing tensor definition: {payload['variation_blocked_by_missing_tensor_definition']}",
        f"Variation blocked by missing variational rules: {payload['variation_blocked_by_missing_variational_rules']}",
        f"Split Noether residuals evaluated: {payload['split_noether_residuals_evaluated']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Candidate Rows",
        "",
    ]
    for row in payload["candidate_rows"]:
        lines.append(f"- {row['row']}: `{row['formula']}` ({row['status']})")
    lines.extend(["", f"Weak sign normalization solution: `{payload['weak_sign_normalization_solution']}`"])
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
