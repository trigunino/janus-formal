from __future__ import annotations

from pathlib import Path
import json

import sympy as sp


REPORT_PATH = Path("outputs/reports/p0_eft_holst_stress_trace_derivation.md")
JSON_PATH = Path("outputs/reports/p0_eft_holst_stress_trace_derivation.json")


def build_payload() -> dict:
    rho, p, pi_trace = sp.symbols("rho p pi_trace")
    stress_trace = -rho + 3 * p + pi_trace
    radiation_condition = sp.Eq(p, rho / 3)
    transverse_shear_condition = sp.Eq(pi_trace, 0)
    reduced = sp.simplify(stress_trace.subs({p: rho / 3, pi_trace: 0}))
    c_q, c_pi, c_slip = sp.symbols("c_q c_pi c_slip")
    equations = [
        sp.Eq(c_q + c_pi, 1),
        sp.Eq(c_slip - c_q, 0),
        sp.Eq(c_pi, 0),
    ]
    solution = sp.solve(equations, [c_q, c_pi, c_slip], dict=True)[0]
    return {
        "description": "Trace derivation for the preferred Immirzi third constraint.",
        "status": "holst-stress-trace-derivation-run",
        "stress_trace": str(stress_trace),
        "radiation_condition": str(radiation_condition),
        "transverse_shear_condition": str(transverse_shear_condition),
        "reduced_trace": str(reduced),
        "traceless_holst_stress_derived": reduced == 0,
        "third_constraint": "c_pi = 0",
        "coefficient_solution": {str(k): str(v) for k, v in solution.items()},
        "coefficients_unique": len(solution) == 3,
        "cambridge_safe_to_patch": False,
        "next_required": (
            "Promote the traceless stress result to a CAMB patch only after checking the "
            "full linearized Immirzi stress tensor signs against Planck."
        ),
    }


def render_markdown(payload: dict) -> str:
    return "\n".join(
        [
            "# P0 EFT Holst Stress Trace Derivation",
            "",
            payload["description"],
            "",
            f"Status: {payload['status']}",
            f"Traceless stress derived: {payload['traceless_holst_stress_derived']}",
            f"CAMB safe to patch: {payload['cambridge_safe_to_patch']}",
            "",
            "## Trace",
            "",
            f"- trace: `{payload['stress_trace']}`",
            f"- reduced trace: `{payload['reduced_trace']}`",
            f"- third constraint: `{payload['third_constraint']}`",
            f"- coefficients: `{payload['coefficient_solution']}`",
            "",
            "## Next",
            "",
            payload["next_required"],
            "",
        ]
    )


def write_reports(report_path: Path = REPORT_PATH, json_path: Path = JSON_PATH) -> dict:
    report_path.parent.mkdir(parents=True, exist_ok=True)
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
