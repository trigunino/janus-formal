from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_janus_eos_prho_no_go_vlasov_gate.md")
JSON_PATH = Path("outputs/reports/p0_janus_eos_prho_no_go_vlasov_gate.json")


def build_payload() -> dict:
    counterexamples = [
        {
            "case": "cold_same_density",
            "moments": "rho=rho0, P_ij=0, p=0",
            "lesson": "same density can have zero pressure",
        },
        {
            "case": "warm_isotropic_same_density",
            "moments": "rho=rho0, P_ij=rho0 sigma^2 delta_ij, p=rho0 sigma^2",
            "lesson": "same density can have nonzero pressure",
        },
    ]
    admissible_routes = [
        "solve full Vlasov f and compute p as a moment",
        "derive a Janus distribution family that fixes sigma^2(rho)",
        "use dust only under the explicit p=0 and Pi=0 contract",
    ]
    forbidden_routes = [
        "do not infer p=p(rho) from rho alone",
        "do not tune p(rho) to observations",
        "do not hide velocity dispersion inside Q_det or Q_cross",
    ]
    return {
        "description": "P0 no-go gate for promoting a scalar EOS p(rho) from collisionless Vlasov moments.",
        "status": "eos-prho-no-go-vlasov-gate-open",
        "depends_on": [
            "p0_janus_full_vlasov_moment_closure_contract",
            "p0_janus_kinetic_moment_hierarchy_equations",
        ],
        "counterexamples": counterexamples,
        "admissible_routes": admissible_routes,
        "forbidden_routes": forbidden_routes,
        "scalar_eos_prho_not_implied_by_vlasov": True,
        "eos_prho_source_derived": False,
        "velocity_dispersion_is_independent_moment": True,
        "full_vlasov_replaces_scalar_eos": True,
        "uses_observational_fit": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "A collisionless Janus/Vlasov route does not generally need or imply p(rho). "
            "Pressure is a moment of f; a scalar EOS requires an extra source-derived "
            "distribution law, otherwise full Vlasov is the non-rustine route."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Janus EOS p(rho) No-Go Vlasov Gate",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Scalar EOS p(rho) not implied by Vlasov: {payload['scalar_eos_prho_not_implied_by_vlasov']}",
        f"EOS p(rho) source-derived: {payload['eos_prho_source_derived']}",
        f"Velocity dispersion is independent moment: {payload['velocity_dispersion_is_independent_moment']}",
        f"Full Vlasov replaces scalar EOS: {payload['full_vlasov_replaces_scalar_eos']}",
        f"Uses observational fit: {payload['uses_observational_fit']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Counterexamples",
        "",
        "| case | moments | lesson |",
        "|---|---|---|",
    ]
    for row in payload["counterexamples"]:
        lines.append(f"| {row['case']} | `{row['moments']}` | {row['lesson']} |")
    lines.extend(["", "## Admissible Routes", ""])
    lines.extend(f"- {item}" for item in payload["admissible_routes"])
    lines.extend(["", "## Forbidden Routes", ""])
    lines.extend(f"- {item}" for item in payload["forbidden_routes"])
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
