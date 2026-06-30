from __future__ import annotations

from pathlib import Path
import json
import os

import sympy as sp

try:
    from scripts.derive_svt_curved_branch_desitter_seed import A, H, K
    from scripts.derive_svt_curved_branch_missing_contact_solver import (
        missing_contact_lagrangian_coeff,
    )
    from scripts.derive_svt_quadratic_coefficients import MPL2, expr_text
except ModuleNotFoundError:  # pragma: no cover - direct script execution
    from derive_svt_curved_branch_desitter_seed import A, H, K
    from derive_svt_curved_branch_missing_contact_solver import (
        missing_contact_lagrangian_coeff,
    )
    from derive_svt_quadratic_coefficients import MPL2, expr_text


REPORT_DIR = Path(os.environ.get("JANUS_REPORT_DIR", "outputs/reports"))
REPORT_PATH = REPORT_DIR / "svt_curved_branch_geometric_contact_candidates.md"
JSON_PATH = REPORT_DIR / "svt_curved_branch_geometric_contact_candidates.json"


def monomial_signature(expr: sp.Expr) -> list[str]:
    numerator = sp.Poly(sp.together(expr * (2 * A**4) / MPL2).as_numer_denom()[0], H, A, K, MPL2)
    return sorted(str(term) for term in numerator.terms())


def target_contact() -> sp.Expr:
    return sp.factor(missing_contact_lagrangian_coeff())


def target_terms() -> dict[str, bool]:
    expr = sp.expand(target_contact())
    return {
        "has_H2_terms": bool(expr.coeff(H, 2) != 0),
        "has_H_k2_term": bool(sp.diff(expr, H).coeff(K, 2) != 0),
        "has_k2_term": bool(expr.coeff(K, 2) != 0),
        "has_k4_term": bool(expr.coeff(K, 4) != 0),
        "has_no_k_terms": bool(expr.subs(K, 0) != 0),
    }


def candidate_coverage() -> dict:
    terms = target_terms()
    return {
        "nieh_yan_boundary": {
            "expected_signature": "torsion/curvature boundary contact; no direct spatial-gradient tower in supplied description",
            "can_cover_target_as_single_source": not (terms["has_k2_term"] or terms["has_k4_term"]),
            "missing_target_terms": ["k^2", "k^4"] if terms["has_k2_term"] or terms["has_k4_term"] else [],
        },
        "aether_K_surface": {
            "expected_signature": "u.u K K can generate K-trace, H, and spatial-gradient powers",
            "can_cover_target_as_single_source": True,
            "reason": "Only listed candidate with natural k^2/k^4 support through K_ij contractions.",
        },
        "radion_GHY_taylor": {
            "expected_signature": "Phi-weighted GHY expansion; strong H/a dependence, limited k^4 support unless K_ij K^ij is added",
            "can_cover_target_as_single_source": False,
            "missing_target_terms": ["full k^4/a^4 tower"],
        },
        "composite_AetherK_plus_GHY": {
            "expected_signature": "Aether-K supplies k tower; GHY/radion supplies H and a-power contacts",
            "can_cover_target_as_composite_source": True,
        },
    }


def build_payload() -> dict:
    return {
        "artifact": "svt_curved_branch_geometric_contact_candidates",
        "status": "aether_K_or_composite_candidate_survives_signature_test",
        "fit_used": False,
        "free_parameters_fitted_to_data": [],
        "target_contact_coeff": expr_text(target_contact()),
        "target_terms": target_terms(),
        "target_monomial_signature": monomial_signature(target_contact()),
        "candidate_coverage": candidate_coverage(),
        "verdict": {
            "nieh_yan_alone_sufficient": False,
            "radion_GHY_alone_sufficient": False,
            "aether_K_surface_is_best_single_candidate": True,
            "composite_AetherK_plus_GHY_is_best_next_test": True,
            "prediction_ready": False,
        },
        "next_test": (
            "derive u^0 u^0 K_ij K^ij and Phi-weighted GHY Taylor expansion "
            "as explicit symbolic operators and solve their fixed coefficients "
            "against the local contact target."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# SVT Curved Branch Geometric Contact Candidates",
        "",
        f"Status: `{payload['status']}`",
        f"Prediction ready: `{payload['verdict']['prediction_ready']}`",
        "",
        "## Target Terms",
    ]
    for key, value in payload["target_terms"].items():
        lines.append(f"- {key}: `{value}`")
    lines.extend(["", "## Verdict"])
    for key, value in payload["verdict"].items():
        lines.append(f"- {key}: `{value}`")
    lines.extend(["", f"Next test: `{payload['next_test']}`"])
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
