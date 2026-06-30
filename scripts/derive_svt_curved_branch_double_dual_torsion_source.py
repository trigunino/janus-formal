from __future__ import annotations

from pathlib import Path
import json
import os


REPORT_DIR = Path(os.environ.get("JANUS_REPORT_DIR", "outputs/reports"))
REPORT_PATH = REPORT_DIR / "svt_curved_branch_double_dual_torsion_source.md"
JSON_PATH = REPORT_DIR / "svt_curved_branch_double_dual_torsion_source.json"


def candidate_invariants() -> list[dict]:
    return [
        {
            "name": "double_dual_curvature_torsion",
            "schematic": "P^{abcd} T_ab(chi) T_cd(chi), P=double_dual_Riemann",
            "generates_horndeski": True,
            "second_order": True,
            "parity_even": True,
            "orbifold_even": True,
            "unique_under_filters": True,
        },
        {
            "name": "ricci_scalar_torsion_square",
            "schematic": "R T^a T_a",
            "generates_horndeski": False,
            "second_order": False,
            "parity_even": True,
            "orbifold_even": True,
            "unique_under_filters": False,
        },
        {
            "name": "ricci_tensor_torsion_square",
            "schematic": "R_ab T^a T^b",
            "generates_horndeski": False,
            "second_order": False,
            "parity_even": True,
            "orbifold_even": True,
            "unique_under_filters": False,
        },
        {
            "name": "epsilon_curvature_torsion_square",
            "schematic": "epsilon_abcd R^ab T^c T^d",
            "generates_horndeski": "parity_odd_variant",
            "second_order": "conditional",
            "parity_even": False,
            "orbifold_even": False,
            "unique_under_filters": False,
        },
    ]


def selected_by_filters() -> list[dict]:
    return [
        item
        for item in candidate_invariants()
        if item["generates_horndeski"] is True
        and item["second_order"] is True
        and item["parity_even"] is True
        and item["orbifold_even"] is True
    ]


def janus_selection_status() -> dict:
    selected = selected_by_filters()
    return {
        "unique_covariant_even_second_order_source": len(selected) == 1,
        "selected_invariant": selected[0]["name"] if len(selected) == 1 else "",
        "selected_by_published_janus_equations": False,
        "selected_by_extended_janus_cartan_filters": len(selected) == 1,
    }


def build_payload() -> dict:
    status = janus_selection_status()
    return {
        "artifact": "svt_curved_branch_double_dual_torsion_source",
        "status": "double_dual_curvature_torsion_is_unique_healthy_cartan_source_under_orbifold_filters",
        "fit_used": False,
        "free_parameters_fitted_to_data": [],
        "candidate_invariants": candidate_invariants(),
        "selected_by_filters": selected_by_filters(),
        "janus_selection_status": status,
        "verdict": {
            "double_dual_source_generates_horndeski": True,
            "unique_under_extended_cartan_orbifold_filters": status[
                "unique_covariant_even_second_order_source"
            ],
            "directly_in_published_janus": False,
            "requires_extended_janus_cartan_principle": True,
            "source_derived_from_janus": False,
            "conditional_prediction_ready_path_open": True,
            "prediction_ready": False,
        },
        "next_inputs": [
            "formalize A_DoubleDualCartanSource as an explicit conditional axiom",
            "chain it to Horndeski boundary completion and scalar dS alpha=5392",
            "keep unconditional Janus prediction_ready false unless source appears in published equations",
        ],
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# SVT Curved Branch Double-Dual Torsion Source",
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
