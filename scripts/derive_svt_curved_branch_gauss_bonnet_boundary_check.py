from __future__ import annotations

from pathlib import Path
import json
import os

import sympy as sp

try:
    from scripts.derive_svt_curved_branch_boundary_derivative_invariant_search import (
        gradient_decomposition,
    )
    from scripts.derive_svt_curved_branch_desitter_seed import A, H, K
    from scripts.derive_svt_quadratic_coefficients import MPL2, expr_text
except ModuleNotFoundError:  # pragma: no cover - direct script execution
    from derive_svt_curved_branch_boundary_derivative_invariant_search import (
        gradient_decomposition,
    )
    from derive_svt_curved_branch_desitter_seed import A, H, K
    from derive_svt_quadratic_coefficients import MPL2, expr_text


REPORT_DIR = Path(os.environ.get("JANUS_REPORT_DIR", "outputs/reports"))
REPORT_PATH = REPORT_DIR / "svt_curved_branch_gauss_bonnet_boundary_check.md"
JSON_PATH = REPORT_DIR / "svt_curved_branch_gauss_bonnet_boundary_check.json"


ALPHA_GB, C_DK, C_D2K = sp.symbols("alpha_GB c_DK c_D2K")


def standard_gauss_bonnet_boundary_families() -> dict[str, bool]:
    return {
        "intrinsic_Einstein_tensor_times_K": True,
        "cubic_extrinsic_curvature_terms": True,
        "D_i_K_D_i_K": False,
        "laplacian_K_squared": False,
    }


def required_gradient_families() -> dict[str, bool]:
    parts = gradient_decomposition()
    return {
        "needs_no_gradient_block": parts["no_spatial_gradient"] != 0,
        "needs_D_i_K_D_i_K_like_block": parts["D_K_D_K_like"] != 0,
        "needs_laplacian_K_squared_like_block": parts["Delta_K_squared_like"] != 0,
    }


def gb_only_can_close_required_target() -> bool:
    gb = standard_gauss_bonnet_boundary_families()
    req = required_gradient_families()
    return not (
        req["needs_D_i_K_D_i_K_like_block"] and not gb["D_i_K_D_i_K"]
        or req["needs_laplacian_K_squared_like_block"] and not gb["laplacian_K_squared"]
    )


def extended_boundary_ansatz_coefficients() -> dict[str, str]:
    parts = gradient_decomposition()
    return {
        "standard_GB_like_low_derivative_block": expr_text(parts["no_spatial_gradient"]),
        "extra_D_i_K_D_i_K_coefficient": expr_text(parts["D_K_D_K_like"]),
        "extra_laplacian_K_squared_coefficient": expr_text(parts["Delta_K_squared_like"]),
    }


def ward_identity_status() -> dict[str, bool]:
    coeffs = gradient_decomposition()
    return {
        "coefficients_are_unique_by_inverse_decomposition": True,
        "coefficients_are_constant_couplings": not bool(
            set().union(*(sp.factor(value).free_symbols for value in coeffs.values()))
            & {A, H, MPL2}
        ),
        "ward_identity_derived_here": False,
    }


def build_payload() -> dict:
    return {
        "artifact": "svt_curved_branch_gauss_bonnet_boundary_check",
        "status": "gauss_bonnet_boundary_is_not_sufficient_without_extra_derivative_boundary_terms",
        "fit_used": False,
        "free_parameters_fitted_to_data": [],
        "standard_gauss_bonnet_boundary_families": standard_gauss_bonnet_boundary_families(),
        "required_gradient_families": required_gradient_families(),
        "gb_only_can_close_required_target": gb_only_can_close_required_target(),
        "extended_boundary_ansatz_coefficients": extended_boundary_ansatz_coefficients(),
        "ward_identity_status": ward_identity_status(),
        "verdict": {
            "standard_lovelock_GB_boundary_sufficient": gb_only_can_close_required_target(),
            "requires_beyond_GB_boundary_derivative_terms": not gb_only_can_close_required_target(),
            "ward_identity_fixes_coefficients": False,
            "source_derived_from_janus": False,
            "prediction_ready": False,
        },
        "next_inputs": [
            "derive a Janus boundary action that contains D_i K D^i K and (Delta K)^2",
            "or prove a Ward identity that forces these terms from a Chern/Gauss-Bonnet extension",
            "without that derivation, treating the coefficients as fixed is still a new extension",
        ],
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# SVT Curved Branch Gauss-Bonnet Boundary Check",
        "",
        f"Status: `{payload['status']}`",
        f"Prediction ready: `{payload['verdict']['prediction_ready']}`",
        "",
        "## Required Families",
    ]
    for key, value in payload["required_gradient_families"].items():
        lines.append(f"- {key}: `{value}`")
    lines.extend(["", "## Verdict"])
    for key, value in payload["verdict"].items():
        lines.append(f"- {key}: `{value}`")
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
