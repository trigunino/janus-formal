from __future__ import annotations

from functools import lru_cache
from pathlib import Path
import json
import os

import sympy as sp

try:
    from scripts.derive_svt_curved_branch_desitter_seed import A, K
    from scripts.derive_svt_curved_branch_longitudinal_aether_check import (
        required_delta_for_constant_alpha,
    )
    from scripts.derive_svt_curved_branch_longitudinal_reduction_rules import (
        normalized_revised_delta_n,
    )
    from scripts.derive_svt_quadratic_coefficients import MPL2, expr_text
except ModuleNotFoundError:  # pragma: no cover - direct script execution
    from derive_svt_curved_branch_desitter_seed import A, K
    from derive_svt_curved_branch_longitudinal_aether_check import (
        required_delta_for_constant_alpha,
    )
    from derive_svt_curved_branch_longitudinal_reduction_rules import (
        normalized_revised_delta_n,
    )
    from derive_svt_quadratic_coefficients import MPL2, expr_text


REPORT_DIR = Path(os.environ.get("JANUS_REPORT_DIR", "outputs/reports"))
REPORT_PATH = REPORT_DIR / "svt_curved_branch_missing_contact_solver.md"
JSON_PATH = REPORT_DIR / "svt_curved_branch_missing_contact_solver.json"

DPSI = sp.Symbol("dpsi")


@lru_cache(maxsize=None)
def missing_delta_n() -> sp.Expr:
    return sp.factor(required_delta_for_constant_alpha() - normalized_revised_delta_n())


@lru_cache(maxsize=None)
def missing_contact_lagrangian_coeff() -> sp.Expr:
    return sp.factor(MPL2 * K**2 * missing_delta_n() / (16 * A**4))


def missing_contact_lagrangian() -> sp.Expr:
    return sp.factor(missing_contact_lagrangian_coeff() * DPSI**2)


def normalized_missing_contact_delta_n() -> sp.Expr:
    coeff = sp.factor(sp.diff(missing_contact_lagrangian(), DPSI, 2) / 2)
    return sp.factor(16 * A**4 * coeff / (MPL2 * K**2))


def closed_delta_n() -> sp.Expr:
    return sp.factor(normalized_revised_delta_n() + normalized_missing_contact_delta_n())


def denominator_factors(expr: sp.Expr) -> str:
    return expr_text(sp.denom(sp.factor(expr)))


def build_payload() -> dict:
    coeff = missing_contact_lagrangian_coeff()
    closed = closed_delta_n()
    required = required_delta_for_constant_alpha()
    return {
        "artifact": "svt_curved_branch_missing_contact_solver",
        "status": "minimal_local_contact_term_found_but_not_sourced",
        "fit_used": False,
        "free_parameters_fitted_to_data": [],
        "missing_deltaN": expr_text(missing_delta_n()),
        "missing_contact_lagrangian_coeff": expr_text(coeff),
        "missing_contact_denominator": denominator_factors(coeff),
        "missing_contact_has_k_pole": K in sp.denom(coeff).free_symbols,
        "normalized_missing_contact_deltaN": expr_text(normalized_missing_contact_delta_n()),
        "closed_deltaN": expr_text(closed),
        "required_deltaN": expr_text(required),
        "closes_required_delta": sp.simplify(closed - required) == 0,
        "verdict": {
            "local_in_k": K not in sp.denom(coeff).free_symbols,
            "local_in_a_only_denominator": denominator_factors(coeff) == "2*a^4",
            "algebraic_closure_found": sp.simplify(closed - required) == 0,
            "sourced_from_action": False,
            "prediction_ready": False,
        },
        "needed_inputs": [
            "identify a Cartan/de Sitter geometric invariant that yields this contact coefficient",
            "derive the coefficient from the shifted action, not from inverse matching",
            "then promote the contact term from solver artifact to source-derived theorem",
        ],
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# SVT Curved Branch Missing Contact Solver",
        "",
        f"Status: `{payload['status']}`",
        f"Prediction ready: `{payload['verdict']['prediction_ready']}`",
        "",
        f"- missing_contact_lagrangian_coeff: `{payload['missing_contact_lagrangian_coeff']}`",
        f"- missing_contact_denominator: `{payload['missing_contact_denominator']}`",
        f"- missing_contact_has_k_pole: `{payload['missing_contact_has_k_pole']}`",
        f"- closes_required_delta: `{payload['closes_required_delta']}`",
        "",
        "## Needed Inputs",
    ]
    lines.extend(f"- {item}" for item in payload["needed_inputs"])
    return "\n".join(lines)


def write_reports(report_path: Path = REPORT_PATH, json_path: Path = JSON_PATH) -> dict:
    payload = build_payload()
    report_path.parent.mkdir(parents=True, exist_ok=True)
    json_path.parent.mkdir(parents=True, exist_ok=True)
    json_path.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    report_path.write_text(render_markdown(payload), encoding="utf-8")
    return payload


def main() -> None:
    write_reports()
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {JSON_PATH}")


if __name__ == "__main__":
    main()
