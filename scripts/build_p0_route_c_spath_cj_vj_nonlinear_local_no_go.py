from __future__ import annotations

from pathlib import Path
import json
import sys


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_route_c_spath_cj_vj_invariant_filter import (
    build_payload as build_invariant_filter,
)


REPORT_PATH = Path("outputs/reports/p0_route_c_spath_cj_vj_nonlinear_local_no_go.md")
JSON_PATH = Path("outputs/reports/p0_route_c_spath_cj_vj_nonlinear_local_no_go.json")


def build_payload() -> dict:
    invariant_filter = build_invariant_filter()
    invariants = invariant_filter["admissible_invariants"]
    rows = [
        {
            "constraint": "diagonal_scalar_covariance",
            "acts_on": "domain of F_C/F_V",
            "equation_on_function": False,
            "effect": "restricts arguments to admissible scalars I_i",
        },
        {
            "constraint": "PT_mirror_parity",
            "acts_on": "even/odd sector of F_C/F_V",
            "equation_on_function": False,
            "effect": "removes parity-incompatible components but leaves arbitrary even/paired functions",
        },
        {
            "constraint": "same_l_compatibility",
            "acts_on": "allowed L-dependent arguments",
            "equation_on_function": False,
            "effect": "requires one bridge L in all terms; does not choose functional dependence",
        },
        {
            "constraint": "stability_C0_V2",
            "acts_on": "open inequality region in function jet",
            "equation_on_function": False,
            "effect": "requires local sign/convexity conditions, not a unique F",
        },
        {
            "constraint": "weak_field_sign",
            "acts_on": "first jet around background",
            "equation_on_function": False,
            "effect": "can filter wrong signs but leaves higher jets arbitrary",
        },
        {
            "constraint": "missing_source_EL",
            "acts_on": "none",
            "equation_on_function": False,
            "effect": "no Janus Euler/source equation fixes F_C or F_V",
        },
    ]
    explicit_survivor_family = {
        "base": "F_C(I)=alpha+sum_i beta_i I_i + epsilon G_even(I)",
        "potential": "F_V(I)=sum_i lambda_i I_i + epsilon H_even(I)",
        "free_functions": ["G_even", "H_even"],
        "why_survives": (
            "For sufficiently small epsilon, parity and stability filters remain satisfied "
            "on the same local patch while G_even/H_even remain arbitrary."
        ),
    }
    return {
        "description": (
            "Bounded no-go for selecting nonlinear local C_J/V_J functions from "
            "admissibility filters alone."
        ),
        "status": "spath-cj-vj-nonlinear-local-no-go-closed",
        "depends_on": ["p0_route_c_spath_cj_vj_invariant_filter"],
        "admissible_invariants": invariants,
        "functional_family": "C_J=F_C(I_1,...,I_5); V_J=F_V(I_1,...,I_5)",
        "rows": rows,
        "explicit_survivor_family": explicit_survivor_family,
        "nonlinear_local_family_considered": True,
        "arbitrary_functions_survive": True,
        "filters_generate_functional_equation": False,
        "pt_samel_stability_select_unique_function": False,
        "bounded_no_go_closed_for_local_filter_only_family": True,
        "requires_source_equation_for_selection": True,
        "uses_observational_fit": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "PT, same-L, no-fit, weak-field and stability constraints filter the "
            "domain/parity/signs of F_C/F_V, but they do not produce a functional "
            "equation selecting the functions. Arbitrary local even perturbations "
            "survive, so a Janus source/action equation is still required."
        ),
    }


def render_markdown(payload: dict) -> str:
    survivor = payload["explicit_survivor_family"]
    lines = [
        "# P0 Route C S_path C_J/V_J Nonlinear Local No-Go",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Functional family: `{payload['functional_family']}`",
        f"Admissible invariants: `{payload['admissible_invariants']}`",
        f"Arbitrary functions survive: {payload['arbitrary_functions_survive']}",
        f"Filters generate functional equation: {payload['filters_generate_functional_equation']}",
        (
            "PT/same-L/stability select unique function: "
            f"{payload['pt_samel_stability_select_unique_function']}"
        ),
        (
            "Bounded no-go closed for local filter-only family: "
            f"{payload['bounded_no_go_closed_for_local_filter_only_family']}"
        ),
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "| constraint | acts on | equation on function | effect |",
        "|---|---|---:|---|",
    ]
    for row in payload["rows"]:
        lines.append(
            f"| {row['constraint']} | {row['acts_on']} | "
            f"{row['equation_on_function']} | {row['effect']} |"
        )
    lines.extend(
        [
            "",
            "## Explicit Survivor Family",
            "",
            f"- base: `{survivor['base']}`",
            f"- potential: `{survivor['potential']}`",
            f"- free functions: `{survivor['free_functions']}`",
            f"- why survives: {survivor['why_survives']}",
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
