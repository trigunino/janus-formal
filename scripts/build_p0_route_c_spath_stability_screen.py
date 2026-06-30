from __future__ import annotations

from pathlib import Path
import json
import sys

import sympy as sp


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_route_c_minimal_spath_extension_axiom_gate import (
    build_payload as build_minimal_spath,
)
from scripts.build_p0_route_c_spath_same_l_substitution_gate import (
    build_payload as build_same_l,
)


REPORT_PATH = Path("outputs/reports/p0_route_c_spath_stability_screen.md")
JSON_PATH = Path("outputs/reports/p0_route_c_spath_stability_screen.json")


def lorentz_generator() -> sp.Matrix:
    bx, by, bz, rx, ry, rz = sp.symbols("b_x b_y b_z r_x r_y r_z")
    return sp.Matrix(
        [
            [0, bx, by, bz],
            [bx, 0, rz, -ry],
            [by, -rz, 0, rx],
            [bz, ry, -rx, 0],
        ]
    )


def build_payload() -> dict:
    minimal = build_minimal_spath()
    same_l = build_same_l()
    c0, v2 = sp.symbols("C_0 V_2", real=True)
    dgamma, dgamma_s = sp.symbols("delta_gamma delta_gamma_s", real=True)
    path_quadratic = sp.expand(c0 * dgamma_s**2 / 2 + v2 * dgamma**2 / 2)

    xi = lorentz_generator()
    lorentz_killing_quadratic = sp.expand(-sp.Rational(1, 2) * sp.trace(xi * xi))
    positive_algebra_quadratic = sp.expand(sp.Rational(1, 2) * sp.trace(xi.T * xi))

    stability_rows = [
        {
            "sector": "path_mode",
            "quadratic_form": str(path_quadratic),
            "condition": "C_0 > 0 and V_2 >= 0",
            "passed": False,
            "blocker": "C_J/V_J are not source-fixed and no background branch is selected",
        },
        {
            "sector": "lorentz_algebra_naive_invariant",
            "quadratic_form": str(lorentz_killing_quadratic),
            "condition": "must not use an indefinite boost/rotation norm as a positive Hamiltonian",
            "passed": False,
            "blocker": "Killing-like Lorentz algebra norm has opposite boost/rotation signs",
        },
        {
            "sector": "lorentz_algebra_positive_auxiliary",
            "quadratic_form": str(positive_algebra_quadratic),
            "condition": "positive auxiliary algebra metric must be source/gauge justified",
            "passed": False,
            "blocker": "positive Frobenius metric is a choice unless derived from the constrained Hamiltonian",
        },
        {
            "sector": "boundary_modes",
            "quadratic_form": "delta^2 B_PT >= 0 on allowed endpoint variations",
            "condition": "self-adjoint PT/mirror boundary conditions",
            "passed": False,
            "blocker": "PT boundary law is not yet fixed",
        },
        {
            "sector": "caustic_multibranch",
            "quadratic_form": "Jacobian/path Hessian remains non-degenerate or switches to sheet sum",
            "condition": "no uncontrolled caustic or multi-path branch",
            "passed": False,
            "blocker": "multibranch Vlasov/sheet rule remains open",
        },
    ]
    instability_flags = [
        {
            "flag": "path_wrong_sign_kinetic",
            "condition": "C_0 <= 0",
            "meaning": "path selector has ghost/degenerate kinetic response",
        },
        {
            "flag": "path_tachyon",
            "condition": "V_2 < 0",
            "meaning": "selected path branch has tachyonic local mode",
        },
        {
            "flag": "lorentz_indefinite_norm",
            "condition": "using -1/2 Tr(Xi^2) as positive energy",
            "meaning": "boost and rotation modes have opposite signs",
        },
        {
            "flag": "boundary_negative_mode",
            "condition": "delta^2 B_PT < 0",
            "meaning": "endpoint/throat mode destabilizes the selected path",
        },
        {
            "flag": "caustic_uncontrolled",
            "condition": "det(d gamma map)=0 without sheet rule",
            "meaning": "single-path extension becomes multivalued",
        },
    ]
    return {
        "description": (
            "Stability screen for the explicit S_path extension. It checks the "
            "representative path mode, Lorentz-algebra transport modes, boundary "
            "modes and caustic/multibranch risk before any predictive use."
        ),
        "status": "spath-stability-screen-open",
        "depends_on": [
            "p0_route_c_minimal_spath_extension_axiom_gate",
            "p0_route_c_spath_same_l_substitution_gate",
        ],
        "minimal_spath_status": minimal["status"],
        "same_l_status": same_l["status"],
        "path_quadratic_form": str(path_quadratic),
        "path_boundedness_conditions": ["C_0 > 0", "V_2 >= 0"],
        "lorentz_killing_quadratic": str(lorentz_killing_quadratic),
        "positive_algebra_quadratic": str(positive_algebra_quadratic),
        "stability_rows": stability_rows,
        "instability_flags": instability_flags,
        "stability_screen_written": True,
        "path_conditions_written": True,
        "lorentz_naive_invariant_indefinite": True,
        "positive_auxiliary_metric_available": True,
        "positive_auxiliary_metric_source_derived": False,
        "boundary_conditions_fixed": False,
        "caustic_multibranch_control_closed": False,
        "ghost_free_proved": False,
        "tachyon_free_proved": False,
        "stability_screen_closed": False,
        "uses_observational_fit": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "The S_path stability screen is defined but not passed. The path mode "
            "needs C_0>0 and V_2>=0, the naive Lorentz-invariant algebra norm is "
            "indefinite, and any positive transport norm or boundary law must be "
            "source/gauge justified before prediction."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Route C S_path Stability Screen",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Path quadratic form: `{payload['path_quadratic_form']}`",
        f"Path boundedness conditions: `{payload['path_boundedness_conditions']}`",
        f"Lorentz Killing quadratic: `{payload['lorentz_killing_quadratic']}`",
        f"Positive algebra quadratic: `{payload['positive_algebra_quadratic']}`",
        f"Lorentz naive invariant indefinite: {payload['lorentz_naive_invariant_indefinite']}",
        f"Positive auxiliary metric source-derived: {payload['positive_auxiliary_metric_source_derived']}",
        f"Boundary conditions fixed: {payload['boundary_conditions_fixed']}",
        f"Caustic/multibranch control closed: {payload['caustic_multibranch_control_closed']}",
        f"Ghost free proved: {payload['ghost_free_proved']}",
        f"Tachyon free proved: {payload['tachyon_free_proved']}",
        f"Stability screen closed: {payload['stability_screen_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "| sector | quadratic form | condition | passed | blocker |",
        "|---|---|---|---:|---|",
    ]
    for row in payload["stability_rows"]:
        lines.append(
            f"| {row['sector']} | `{row['quadratic_form']}` | {row['condition']} | "
            f"{row['passed']} | {row['blocker']} |"
        )
    lines.extend(["", "## Instability Flags", ""])
    for row in payload["instability_flags"]:
        lines.append(f"- `{row['flag']}` if `{row['condition']}`: {row['meaning']}")
    lines.extend(["", f"Verdict: {payload['verdict']}", ""])
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
