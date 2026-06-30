from __future__ import annotations

from pathlib import Path
import json
import os


REPORT_DIR = Path(os.environ.get("JANUS_REPORT_DIR", "outputs/reports"))
REPORT_PATH = REPORT_DIR / "svt_curved_branch_cartan_torsion_horndeski_audit.md"
JSON_PATH = REPORT_DIR / "svt_curved_branch_cartan_torsion_horndeski_audit.json"


def minimal_einstein_cartan_reduction() -> dict:
    return {
        "input_connection": "Gamma = LeviCivita(g) + Contorsion(dchi)",
        "ricci_scalar_split": "R(Gamma)=R(g)+K*K+div(K)",
        "curvature_times_dchi2_generated": False,
        "generated_terms": ["R(g)", "(dchi)^2-like torsion quadratic", "boundary divergence"],
    }


def horndeski_term_requirement() -> dict:
    return {
        "target": "G_mn nabla^m chi nabla^n chi",
        "requires_curvature_tensor_factor": True,
        "requires_nonminimal_double_dual_or_horndeski_structure": True,
        "generated_by_minimal_EC_contorsion_substitution": False,
    }


def viable_cartan_routes() -> list[dict]:
    return [
        {
            "name": "minimal_Einstein_Cartan_with_algebraic_torsion",
            "can_force_horndeski": False,
            "reason": "K*K has no Einstein-tensor curvature factor.",
        },
        {
            "name": "Nieh_Yan_or_torsion_boundary",
            "can_force_horndeski": False,
            "reason": "can source boundary/topological terms, not bulk G_mn dchi dchi by itself.",
        },
        {
            "name": "nonminimal_double_dual_curvature_torsion",
            "can_force_horndeski": True,
            "reason": "double-dual Riemann contractions are the known covariant path to Horndeski derivative coupling.",
        },
        {
            "name": "teleparallel_torsion_scalar_boundary_equivalent",
            "can_force_horndeski": "conditional",
            "reason": "possible only with a specified torsion-scalar coupling, still an extension unless Janus fixes it.",
        },
    ]


def build_payload() -> dict:
    minimal = minimal_einstein_cartan_reduction()
    target = horndeski_term_requirement()
    return {
        "artifact": "svt_curved_branch_cartan_torsion_horndeski_audit",
        "status": "minimal_cartan_torsion_does_not_endogenously_force_horndeski",
        "fit_used": False,
        "free_parameters_fitted_to_data": [],
        "minimal_einstein_cartan_reduction": minimal,
        "horndeski_term_requirement": target,
        "viable_cartan_routes": viable_cartan_routes(),
        "verdict": {
            "text_claim_valid_as_written": False,
            "minimal_cartan_pure_janus_sufficient": False,
            "needs_nonminimal_curvature_torsion_principle": True,
            "horndeski_still_unique_healthy_candidate": True,
            "source_derived_from_janus": False,
            "prediction_ready": False,
        },
        "next_inputs": [
            "test a double-dual curvature-torsion invariant as the nonminimal Cartan source",
            "check whether Janus orbifold symmetry uniquely selects that invariant",
            "do not mark Horndeski source-derived from minimal Einstein-Cartan alone",
        ],
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# SVT Curved Branch Cartan Torsion Horndeski Audit",
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
