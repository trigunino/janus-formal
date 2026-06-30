from __future__ import annotations

from pathlib import Path
import json

import sympy as sp


REPORT_PATH = Path("outputs/reports/p0_local_phi_scouple_symbolic_restricted_audit.md")
JSON_PATH = Path("outputs/reports/p0_local_phi_scouple_symbolic_restricted_audit.json")


def build_payload() -> dict:
    i_metric, i_matter, c1, c2, c3 = sp.symbols("I_metric I_matter c1 c2 c3")
    linear = c1 * i_matter
    quadratic_metric = c1 * i_matter + c2 * (i_metric - 4) ** 2
    mixed = c1 * i_matter + c2 * (i_metric - 4) ** 2 + c3 * (i_metric - 4) * i_matter
    weak_surface = {i_metric: 4}
    same_linear_limit = [
        {
            "candidate": "linear_cross_matter",
            "phi": str(linear),
            "weak_surface_value": str(sp.simplify(linear.subs(weak_surface))),
            "same_linear_limit_as_linear": bool(sp.simplify(linear.subs(weak_surface) - linear.subs(weak_surface)) == 0),
        },
        {
            "candidate": "quadratic_metric_deformation",
            "phi": str(quadratic_metric),
            "weak_surface_value": str(sp.simplify(quadratic_metric.subs(weak_surface))),
            "same_linear_limit_as_linear": bool(
                sp.simplify(quadratic_metric.subs(weak_surface) - linear.subs(weak_surface)) == 0
            ),
        },
        {
            "candidate": "mixed_metric_matter_deformation",
            "phi": str(mixed),
            "weak_surface_value": str(sp.simplify(mixed.subs(weak_surface))),
            "same_linear_limit_as_linear": bool(
                sp.simplify(mixed.subs(weak_surface) - linear.subs(weak_surface)) == 0
            ),
        },
    ]
    obstruction = (
        all(row["same_linear_limit_as_linear"] for row in same_linear_limit)
        and str(quadratic_metric) != str(linear)
        and str(mixed) != str(linear)
    )
    noether_model_constraints = [
        {
            "constraint": "dPhi/dI_metric at weak surface must vanish",
            "effect": "kills linear metric deformation at I_metric=4",
            "solves": str(sp.solve([sp.diff(mixed, i_metric).subs(weak_surface)], [c3], dict=True)),
            "source_derived": False,
        },
        {
            "constraint": "second metric deformation coefficient must vanish",
            "effect": "kills quadratic metric deformation",
            "solves": str(sp.solve([c2], [c2], dict=True)),
            "source_derived": False,
        },
    ]
    noether_reduced_unique = True
    return {
        "description": "Restricted symbolic audit for local low-derivative Phi/S_couple no-go.",
        "status": "restricted-symbolic-family-obstruction-confirmed",
        "assumptions": [
            "scalar local Phi(I_metric,I_matter)",
            "weak aligned surface I_metric=4",
            "same weak-field matter linearization",
            "no split Noether equations imposed yet",
        ],
        "same_linear_limit_candidates": same_linear_limit,
        "nonunique_candidates_exist": obstruction,
        "noether_model_constraints": noether_model_constraints,
        "noether_reduced_unique_if_imposed": noether_reduced_unique,
        "noether_constraints_source_derived": False,
        "split_noether_calculable_target_available": True,
        "no_go_proved": False,
        "reason_no_go_not_proved": (
            "Restricted symbolic expansion shows multiple local candidates share the same weak-field "
            "linear limit. Model Noether-like constraints can eliminate the displayed deformations only "
            "when imposed; the actual Split Noether residual equations are still needed."
        ),
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "The restricted symbolic check supports the family obstruction rather than a no-go theorem: "
            "weak-field and mirror-compatible scalar data alone do not force unique Phi."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Local Phi/S_couple Symbolic Restricted Audit",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Nonunique candidates exist: {payload['nonunique_candidates_exist']}",
        f"No-go proved: {payload['no_go_proved']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Assumptions",
        "",
    ]
    lines.extend(f"- {item}" for item in payload["assumptions"])
    lines.extend(["", "## Same Linear-Limit Candidates", ""])
    for row in payload["same_linear_limit_candidates"]:
        lines.append(f"- {row['candidate']}: `{row['phi']}`")
        lines.append(f"  - weak surface value: `{row['weak_surface_value']}`")
        lines.append(f"  - same linear limit: {row['same_linear_limit_as_linear']}")
    lines.extend(["", "## Model Noether Constraints", ""])
    for row in payload["noether_model_constraints"]:
        lines.append(f"- {row['constraint']}: {row['effect']}")
        lines.append(f"  - solves: `{row['solves']}`")
        lines.append(f"  - source derived: {row['source_derived']}")
    lines.append(f"Noether-reduced unique if imposed: {payload['noether_reduced_unique_if_imposed']}")
    lines.append(f"Noether constraints source-derived: {payload['noether_constraints_source_derived']}")
    lines.append(f"Split Noether calculable target available: {payload['split_noether_calculable_target_available']}")
    lines.extend(
        [
            "",
            f"Reason no-go not proved: {payload['reason_no_go_not_proved']}",
            "",
            f"Verdict: {payload['verdict']}",
            "",
        ]
    )
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
