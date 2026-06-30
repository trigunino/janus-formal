from __future__ import annotations

from pathlib import Path
import json
import os

import sympy as sp

try:
    from scripts.derive_svt_curved_branch_radion_bulk_source_candidates import (
        horndeski_boundary_completion_signature,
        horndeski_bulk_signature,
        target_families,
    )
    from scripts.derive_svt_quadratic_coefficients import expr_text
except ModuleNotFoundError:  # pragma: no cover - direct script execution
    from derive_svt_curved_branch_radion_bulk_source_candidates import (
        horndeski_boundary_completion_signature,
        horndeski_bulk_signature,
        target_families,
    )
    from derive_svt_quadratic_coefficients import expr_text


REPORT_DIR = Path(os.environ.get("JANUS_REPORT_DIR", "outputs/reports"))
REPORT_PATH = REPORT_DIR / "svt_curved_branch_horndeski_boundary_completion.md"
JSON_PATH = REPORT_DIR / "svt_curved_branch_horndeski_boundary_completion.json"


def covariant_completion_principles() -> dict[str, bool]:
    return {
        "second_order_field_equations_required": True,
        "dirichlet_variational_principle_required": True,
        "normal_derivative_boundary_terms_required": True,
        "coefficient_independent_of_bulk_horndeski_coupling": False,
    }


def completion_ratio_to_bulk() -> dict[str, str | bool]:
    bulk = horndeski_bulk_signature()
    boundary = horndeski_boundary_completion_signature()
    target = target_families()
    return {
        "bulk_D_K_D_K_matches_target": sp.simplify(bulk["D_K_D_K_like"] - target["D_K_D_K_like"]) == 0,
        "boundary_Delta_K_squared_matches_target": sp.simplify(
            boundary["Delta_K_squared_like"] - target["Delta_K_squared_like"]
        )
        == 0,
        "same_unit_coupling_required": "eta=bnd=1",
        "boundary_completion_coeff": expr_text(boundary["Delta_K_squared_like"]),
        "bulk_horndeski_coeff": expr_text(bulk["D_K_D_K_like"]),
    }


def source_derivation_status() -> dict[str, bool]:
    principles = covariant_completion_principles()
    ratio = completion_ratio_to_bulk()
    return {
        "completion_required_by_variational_principle": all(principles.values()) is False
        and principles["normal_derivative_boundary_terms_required"],
        "symbolic_family_matches_target": bool(ratio["boundary_Delta_K_squared_matches_target"]),
        "coefficient_fixed_relative_to_bulk_if_horndeski_action_accepted": True,
        "janus_source_provides_horndeski_action": False,
    }


def build_payload() -> dict:
    status = source_derivation_status()
    return {
        "artifact": "svt_curved_branch_horndeski_boundary_completion",
        "status": "horndeski_boundary_completion_closes_k4_if_horndeski_bulk_action_is_accepted",
        "fit_used": False,
        "free_parameters_fitted_to_data": [],
        "covariant_completion_principles": covariant_completion_principles(),
        "completion_ratio_to_bulk": completion_ratio_to_bulk(),
        "source_derivation_status": status,
        "verdict": {
            "boundary_completion_is_required_by_horndeski_variation": status[
                "completion_required_by_variational_principle"
            ],
            "boundary_completion_closes_k4_block": status["symbolic_family_matches_target"],
            "coefficient_is_fixed_conditionally": status[
                "coefficient_fixed_relative_to_bulk_if_horndeski_action_accepted"
            ],
            "requires_new_horndeski_radion_axiom": not status["janus_source_provides_horndeski_action"],
            "source_derived_from_janus": False,
            "prediction_ready": False,
        },
        "next_inputs": [
            "find or derive Janus reason for adding the covariant Horndeski radion coupling",
            "if accepted as extension, mark it explicitly as A_HorndeskiRadionExtension",
            "then promote the completed scalar dS stability theorem to conditional prediction_ready",
        ],
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# SVT Curved Branch Horndeski Boundary Completion",
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
