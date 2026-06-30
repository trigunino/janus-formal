from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_noncomoving_momentum_t0i_closure_target.md")
JSON_PATH = Path("outputs/reports/p0_noncomoving_momentum_t0i_closure_target.json")


def build_payload() -> dict:
    formulas = {
        "perfect_fluid_t0i": "T0i=(rho+p) gamma^2 beta_i + Pi0i",
        "dust_limit": "T0i=rho gamma^2 beta_i",
        "comoving_limit": "beta_i=0 and Pi0i=0 => T0i=0",
    }
    requirements = [
        "derive beta_i from Janus source dynamics",
        "derive p_cross or prove pressure branch is negligible",
        "transport Pi0i/Pi00 or prove the eigenframe keeps them zero",
        "substitute T0i into R_plus/R_minus momentum components",
        "keep momentum closure separate from scalar Q_det/Q_cross",
    ]
    decision = {
        "t0i_formula_target_defined": True,
        "dust_limit_checked": True,
        "source_derived_beta_available": False,
        "pressure_pi_momentum_transport_closed": False,
        "r_plus_momentum_closed": False,
        "r_minus_momentum_closed": False,
    }
    return {
        "description": "P0 target for non-comoving momentum closure via T0i.",
        "status": "momentum-closure-target-open",
        "formulas": formulas,
        "requirements": requirements,
        "decision": decision,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "Boosted T00 alone cannot close non-comoving matter. Momentum T0i must "
            "be transported and cancelled in both Bianchi residuals."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Non-comoving Momentum T0i Closure Target",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Formulas",
        "",
    ]
    lines.extend(f"- {key}: `{value}`" for key, value in payload["formulas"].items())
    lines.extend(["", "## Requirements", ""])
    lines.extend(f"- {item}" for item in payload["requirements"])
    lines.extend(["", "## Decision", ""])
    lines.extend(f"- {key}: {value}" for key, value in payload["decision"].items())
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
