from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_eft_minimal_bulk_operator_plan.md")
JSON_PATH = Path("outputs/reports/p0_eft_minimal_bulk_operator_plan.json")


def build_payload() -> dict:
    candidate_operators = [
        {
            "id": "D_scalar",
            "operator": "-nabla^2 + M^2 + c_R R + c_chi (nabla chi)^2",
            "can_generate_double_dual": False,
            "reason": "scalar Laplace-type operator generates curvature-radion tower, but not uniquely Horndeski without projection assumptions",
        },
        {
            "id": "D_dirac_cartan",
            "operator": "i gamma^a e_a^mu (nabla_mu + omega_mu + axial_torsion_mu(chi)) - M",
            "can_generate_double_dual": "possible",
            "reason": "Dirac operator with Cartan torsion has known heat-kernel sensitivity to curvature and torsion",
        },
        {
            "id": "D_vector_aether",
            "operator": "Proca/Maxwell-type operator on orbifold with radion-dependent timelike leg",
            "can_generate_double_dual": "possible",
            "reason": "can generate curvature-vector/radion operators, but gauge fixing and ghosts must be handled",
        },
    ]
    recommended_first_test = {
        "operator": "D_dirac_cartan",
        "why": "minimal Cartan-sensitive heat-kernel test; fermions naturally couple to spin connection and torsion",
        "expected_output": "whether curvature-torsion/radion Seeley-DeWitt terms contain the double-dual/Horndeski structure",
        "not_enough_for_final_prediction": "needs actual Janus bulk spectrum and coefficient sum over species",
    }
    theorem_status = {
        "minimal_operator_plan_written": True,
        "operator_chosen_for_first_test": True,
        "actual_heat_kernel_coefficients_computed": False,
        "species_sum_known": False,
        "prediction_ready": False,
    }
    return {
        "description": "Minimal EFT operator plan for the first non-classical double-dual source test.",
        "status": "first-test-operator-selected-not-computed",
        "theorem_status": theorem_status,
        "candidate_operators": candidate_operators,
        "recommended_first_test": recommended_first_test,
        "next_steps": [
            "write a symbolic Dirac-Cartan heat-kernel target for a2/a4 terms",
            "track which coefficient families can produce G_mn dchi^m dchi^n",
            "separate generated operator existence from exact coefficient matching",
        ],
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 EFT Minimal Bulk Operator Plan",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
    ]
    lines.extend(f"{key}: {value}" for key, value in payload["theorem_status"].items())
    lines.extend(["", "## Candidate Operators"])
    for row in payload["candidate_operators"]:
        lines.append(f"- {row['id']}: {row['operator']} -> {row['can_generate_double_dual']}")
    lines.extend(["", "## Recommended First Test"])
    for key, value in payload["recommended_first_test"].items():
        lines.append(f"- {key}: {value}")
    lines.extend(["", "## Next Steps"])
    lines.extend(f"- {item}" for item in payload["next_steps"])
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
