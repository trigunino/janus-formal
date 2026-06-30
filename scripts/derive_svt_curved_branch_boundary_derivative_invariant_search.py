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
REPORT_PATH = REPORT_DIR / "svt_curved_branch_boundary_derivative_invariant_search.md"
JSON_PATH = REPORT_DIR / "svt_curved_branch_boundary_derivative_invariant_search.json"


def target_coeff() -> sp.Expr:
    return sp.factor(missing_contact_lagrangian_coeff())


def gradient_decomposition() -> dict[str, sp.Expr]:
    target = sp.Poly(sp.expand(target_coeff()), K)
    return {
        "no_spatial_gradient": sp.factor(target.coeff_monomial(K**0)),
        "D_K_D_K_like": sp.factor(target.coeff_monomial(K**2)),
        "Delta_K_squared_like": sp.factor(target.coeff_monomial(K**4)),
    }


def low_order_boundary_span_has_target() -> bool:
    parts = gradient_decomposition()
    return parts["D_K_D_K_like"] == 0 and parts["Delta_K_squared_like"] == 0


def derivative_boundary_extension_candidate() -> dict[str, str]:
    parts = gradient_decomposition()
    return {
        "K_squared_family": expr_text(parts["no_spatial_gradient"]),
        "D_i_K_D_i_K_family": expr_text(parts["D_K_D_K_like"]),
        "laplacian_K_squared_family": expr_text(parts["Delta_K_squared_like"]),
    }


def coefficient_is_constant(expr: sp.Expr) -> bool:
    return not bool(sp.factor(expr).free_symbols & {A, H, MPL2})


def build_payload() -> dict:
    parts = gradient_decomposition()
    extension = derivative_boundary_extension_candidate()
    constant_coefficients = {
        key: coefficient_is_constant(value)
        for key, value in parts.items()
    }
    return {
        "artifact": "svt_curved_branch_boundary_derivative_invariant_search",
        "status": "local_boundary_derivative_extension_identified_not_janus_sourced",
        "fit_used": False,
        "free_parameters_fitted_to_data": [],
        "target_contact_coeff": expr_text(target_coeff()),
        "gradient_decomposition": {
            key: expr_text(value)
            for key, value in parts.items()
        },
        "constant_coefficient_by_family": constant_coefficients,
        "candidate_extension": extension,
        "verdict": {
            "low_order_K_only_boundary_terms_sufficient": low_order_boundary_span_has_target(),
            "requires_spatial_derivatives_of_extrinsic_curvature": parts["D_K_D_K_like"] != 0
            or parts["Delta_K_squared_like"] != 0,
            "requires_nonconstant_background_coefficients": not all(constant_coefficients.values()),
            "mathematical_local_extension_exists": True,
            "source_derived_from_janus": False,
            "prediction_ready": False,
        },
        "next_inputs": [
            "derive whether Janus/Cartan orbifold action allows boundary operators D_i K D^i K and (Delta K)^2",
            "if allowed, derive their coefficients from a boundary action instead of inverse decomposition",
            "if not allowed, the dS closure target is a no-go for low-order boundary geometry",
        ],
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# SVT Curved Branch Boundary Derivative Invariant Search",
        "",
        f"Status: `{payload['status']}`",
        f"Prediction ready: `{payload['verdict']['prediction_ready']}`",
        "",
        "## Gradient Decomposition",
    ]
    for key, value in payload["gradient_decomposition"].items():
        lines.append(f"- {key}: `{value}`")
    lines.extend(["", "## Verdict"])
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
