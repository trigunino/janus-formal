from __future__ import annotations

from pathlib import Path
import json
import os

import sympy as sp

try:
    from scripts.derive_svt_curved_branch_boundary_derivative_invariant_search import (
        gradient_decomposition,
    )
    from scripts.derive_svt_curved_branch_missing_contact_solver import (
        missing_contact_lagrangian_coeff,
    )
    from scripts.derive_svt_curved_branch_desitter_seed import A, H, K
    from scripts.derive_svt_quadratic_coefficients import MPL2, expr_text
except ModuleNotFoundError:  # pragma: no cover - direct script execution
    from derive_svt_curved_branch_boundary_derivative_invariant_search import (
        gradient_decomposition,
    )
    from derive_svt_curved_branch_missing_contact_solver import (
        missing_contact_lagrangian_coeff,
    )
    from derive_svt_curved_branch_desitter_seed import A, H, K
    from derive_svt_quadratic_coefficients import MPL2, expr_text


REPORT_DIR = Path(os.environ.get("JANUS_REPORT_DIR", "outputs/reports"))
REPORT_PATH = REPORT_DIR / "svt_curved_branch_anomaly_vs_stueckelberg_discriminator.md"
JSON_PATH = REPORT_DIR / "svt_curved_branch_anomaly_vs_stueckelberg_discriminator.json"


def target() -> sp.Expr:
    return sp.factor(missing_contact_lagrangian_coeff())


def a_power_span(expr: sp.Expr) -> list[int]:
    terms = sp.Poly(sp.together(expr).as_numer_denom()[0], A, H, K, MPL2).terms()
    denom_power = sp.degree(sp.together(expr).as_numer_denom()[1], A)
    return sorted({int(powers[0] - denom_power) for powers, coeff in terms if coeff != 0})


def family_power_summary() -> dict[str, list[int]]:
    parts = gradient_decomposition()
    return {key: a_power_span(value) for key, value in parts.items()}


def has_h_power(expr: sp.Expr, power: int) -> bool:
    numerator = sp.together(expr).as_numer_denom()[0]
    return any(
        powers[0] == power and coeff != 0
        for powers, coeff in sp.Poly(sp.expand(numerator), H, A, K, MPL2).terms()
    )


def discriminant_features() -> dict[str, bool | list[int]]:
    powers = a_power_span(target())
    parts = gradient_decomposition()
    return {
        "target_has_log_a": False,
        "target_has_multiple_polynomial_a_powers": len(powers) > 1,
        "target_has_H2_background_terms": has_h_power(parts["no_spatial_gradient"], 2),
        "target_has_H_times_k2_terms": has_h_power(parts["D_K_D_K_like"], 1),
        "target_has_pure_k4_boundary_laplacian_term": parts["Delta_K_squared_like"] != 0,
        "target_a_power_span": powers,
    }


def route_scores() -> dict[str, dict[str, bool | str]]:
    features = discriminant_features()
    anomaly_matches = (
        features["target_has_log_a"]
        and features["target_has_pure_k4_boundary_laplacian_term"]
        and not features["target_has_H2_background_terms"]
    )
    stueckelberg_matches = (
        features["target_has_multiple_polynomial_a_powers"]
        and features["target_has_H2_background_terms"]
        and features["target_has_H_times_k2_terms"]
    )
    return {
        "ward_chern_anomaly_route": {
            "matches_observed_scaling": anomaly_matches,
            "blocking_feature": "target is polynomial in a,H and has H^2 background terms, not a clean log(det ratio) signature",
        },
        "bulk_radion_stueckelberg_route": {
            "matches_observed_scaling": stueckelberg_matches,
            "blocking_feature": "not blocked by scaling; still needs explicit source action and coefficient derivation",
        },
    }


def build_payload() -> dict:
    scores = route_scores()
    return {
        "artifact": "svt_curved_branch_anomaly_vs_stueckelberg_discriminator",
        "status": "scaling_prefers_bulk_radion_stueckelberg_over_pure_anomaly",
        "fit_used": False,
        "free_parameters_fitted_to_data": [],
        "target_contact_coeff": expr_text(target()),
        "family_power_summary": family_power_summary(),
        "discriminant_features": discriminant_features(),
        "route_scores": scores,
        "verdict": {
            "pure_ward_chern_anomaly_supported_by_scaling": scores["ward_chern_anomaly_route"]["matches_observed_scaling"],
            "bulk_radion_stueckelberg_supported_by_scaling": scores["bulk_radion_stueckelberg_route"]["matches_observed_scaling"],
            "source_derived_from_janus": False,
            "prediction_ready": False,
        },
        "next_inputs": [
            "derive a classical radion non-minimal bulk term and project it to the boundary",
            "test xi*chi*R and Horndeski/Galileon-like chi*G_mn*nabla^m*nabla^n chi candidates",
            "reject pure anomaly unless a log determinant source is explicitly found",
        ],
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# SVT Curved Branch Anomaly vs Stueckelberg Discriminator",
        "",
        f"Status: `{payload['status']}`",
        f"Prediction ready: `{payload['verdict']['prediction_ready']}`",
        "",
        "## Verdict",
    ]
    for key, value in payload["verdict"].items():
        lines.append(f"- {key}: `{value}`")
    lines.extend(["", "## Next Inputs"])
    lines.extend(f"- {item}" for item in payload["next_inputs"])
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
