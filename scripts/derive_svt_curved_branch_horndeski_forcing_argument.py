from __future__ import annotations

from pathlib import Path
import json
import os

try:
    from scripts.derive_svt_quadratic_coefficients import expr_text
except ModuleNotFoundError:  # pragma: no cover - direct script execution
    from derive_svt_quadratic_coefficients import expr_text


REPORT_DIR = Path(os.environ.get("JANUS_REPORT_DIR", "outputs/reports"))
REPORT_PATH = REPORT_DIR / "svt_curved_branch_horndeski_forcing_argument.md"
JSON_PATH = REPORT_DIR / "svt_curved_branch_horndeski_forcing_argument.json"


def candidate_classes() -> list[dict]:
    return [
        {
            "name": "minimal_radion_kinetic_potential",
            "second_order_eom": True,
            "generates_curvature_boundary_derivative_contact": False,
            "reason_rejected": "cannot generate D_i K D^i K or (Delta K)^2",
        },
        {
            "name": "xi_chi_R",
            "second_order_eom": True,
            "generates_curvature_boundary_derivative_contact": False,
            "reason_rejected": "covers background curvature block only",
        },
        {
            "name": "generic_R2_or_RmnRmn",
            "second_order_eom": False,
            "generates_curvature_boundary_derivative_contact": True,
            "reason_rejected": "adds higher-derivative metric equations and ghost risk",
        },
        {
            "name": "generic_second_derivative_scalar_couplings",
            "second_order_eom": False,
            "generates_curvature_boundary_derivative_contact": True,
            "reason_rejected": "not Horndeski-degenerate; unsafe without new constraint algebra",
        },
        {
            "name": "einstein_tensor_derivative_coupling",
            "form": "G_mn nabla^m chi nabla^n chi or equivalent integrated chi G_mn nabla^m nabla^n chi",
            "second_order_eom": True,
            "generates_curvature_boundary_derivative_contact": True,
            "reason_rejected": "",
        },
    ]


def survivor_classes() -> list[dict]:
    return [
        item
        for item in candidate_classes()
        if item["second_order_eom"] and item["generates_curvature_boundary_derivative_contact"]
    ]


def forcing_status() -> dict:
    survivors = survivor_classes()
    return {
        "unique_survivor_under_local_second_order_scalar_tensor_assumptions": len(survivors) == 1,
        "survivor": survivors[0]["name"] if len(survivors) == 1 else "",
        "still_needs_janus_principle_for_scalar_tensor_assumptions": True,
    }


def build_payload() -> dict:
    status = forcing_status()
    return {
        "artifact": "svt_curved_branch_horndeski_forcing_argument",
        "status": "horndeski_radion_is_unique_survivor_under_second_order_local_scalar_tensor_filter",
        "fit_used": False,
        "free_parameters_fitted_to_data": [],
        "filters": [
            "local covariant radion-metric coupling",
            "second-order field equations",
            "no generic higher-curvature ghost sector",
            "must produce boundary derivative contact after Cartan projection",
            "must admit boundary completion for well-posed variation",
        ],
        "candidate_classes": candidate_classes(),
        "survivors": survivor_classes(),
        "forcing_status": status,
        "verdict": {
            "horndeski_radion_forced_by_filters": status[
                "unique_survivor_under_local_second_order_scalar_tensor_assumptions"
            ],
            "forced_directly_by_published_janus": False,
            "new_axiom_if_filters_not_accepted_as_janus_principle": True,
            "source_derived_from_janus": False,
            "prediction_ready": False,
        },
        "next_inputs": [
            "decide whether Janus-Cartan includes the filter: local second-order scalar-tensor completion of the radion sector",
            "if yes, promote Horndeski-radion as forced conditional closure",
            "if no, it remains a new extension despite being the unique healthy candidate found",
        ],
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# SVT Curved Branch Horndeski Forcing Argument",
        "",
        f"Status: `{payload['status']}`",
        f"Prediction ready: `{payload['verdict']['prediction_ready']}`",
        "",
        "## Verdict",
    ]
    for key, value in payload["verdict"].items():
        lines.append(f"- {key}: `{value}`")
    lines.extend(["", "## Survivors"])
    lines.extend(f"- {item['name']}" for item in payload["survivors"])
    return "\n".join(lines)


def write_reports(report_path: Path = REPORT_PATH, json_path: Path = JSON_PATH) -> dict:
    import json

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
