from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/janus_linear_growth_modes.md")
JSON_PATH = Path("outputs/reports/janus_linear_growth_modes.json")


def build_payload() -> dict:
    basis = [
        {
            "mode": "sum_mode",
            "definition": "delta_null = Omega_minus delta_plus + Omega_plus delta_minus_eff",
            "equation": "delta_null'' + A(a) delta_null' = 0",
            "interpretation": "weighted compensated mode with Omega_plus delta_plus - Omega_minus delta_minus_eff = 0",
            "status": "weak-field eigenmode target",
        },
        {
            "mode": "signed_contrast_mode",
            "definition": "delta_source proportional [1, -1]",
            "equation": "lambda_source = (3/2)(Omega_plus + Omega_minus)",
            "interpretation": "Janus signed source mode that drives Phi_plus",
            "status": "weak-field eigenmode target",
        },
    ]
    operator_inputs = [
        "delta'' + A(a) delta' = M(a) delta",
        "M(a) = (3/2) [[Omega_plus, -Omega_minus], [-Omega_plus, Omega_minus]]",
        "A(a) = 2 + d ln H / d ln a",
        "H(a) = H0 E_J(a)",
        "Omega_abs(a) must be source-derived for the chosen Janus background",
        "delta_minus_eff means the positive-effective density branch; negative_proper requires Q_det first",
    ]
    velocity_closure = [
        "theta_sum = -a H delta_sum'",
        "theta_diff = -a H delta_diff'",
        "u_s(k,a) remains irrotational only in the scalar weak-field branch",
    ]
    no_fit_rules = [
        "do not choose A_J by matching sigma8",
        "do not import a Lambda-CDM transfer function as T_J",
        "do not use Gaussian/lognormal/bounded IC shape as physical transfer evidence",
    ]
    return {
        "description": "Weak-field eigenmode target for Janus two-sector linear growth.",
        "source_anchors": [
            "M15/M30 signed Newtonian source",
            "M18 Janus expansion for E_J(a)",
            "janus_linear_ic_equations_target",
        ],
        "physics_closed": False,
        "basis": basis,
        "operator_inputs": operator_inputs,
        "velocity_closure": velocity_closure,
        "no_fit_rules": no_fit_rules,
        "verdict": (
            "The weak-field two-sector system decomposes into a neutral sum mode and "
            "a signed contrast mode. This is a growth target, not a final transfer "
            "or amplitude normalization."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# Janus Linear Growth Modes",
        "",
        payload["description"],
        "",
        f"Physics closed: {payload['physics_closed']}",
        "",
        "## Modes",
        "",
        "| mode | definition | equation | interpretation | status |",
        "|---|---|---|---|---|",
    ]
    for row in payload["basis"]:
        lines.append(
            f"| {row['mode']} | `{row['definition']}` | `{row['equation']}` | "
            f"{row['interpretation']} | {row['status']} |"
        )
    lines.extend(["", "## Operator Inputs", ""])
    lines.extend(f"- `{item}`" for item in payload["operator_inputs"])
    lines.extend(["", "## Velocity Closure", ""])
    lines.extend(f"- `{item}`" for item in payload["velocity_closure"])
    lines.extend(["", "## No-Fit Rules", ""])
    lines.extend(f"- {item}" for item in payload["no_fit_rules"])
    lines.extend(["", f"Verdict: {payload['verdict']}", ""])
    return "\n".join(lines)


def main() -> None:
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    payload = build_payload()
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(render_markdown(payload), encoding="utf-8")
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {JSON_PATH}")


if __name__ == "__main__":
    main()
