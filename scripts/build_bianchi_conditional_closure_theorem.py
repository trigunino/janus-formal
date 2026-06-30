from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/bianchi_conditional_closure_theorem.md")
JSON_PATH = Path("outputs/reports/bianchi_conditional_closure_theorem.json")


def build_payload() -> dict:
    theorem = {
        "name": "lorentz_dust_transport_conditional_bianchi_closure",
        "claim": (
            "If same-sector dust stresses are conserved, transported continuities hold, "
            "and transported force equations cancel connection-difference terms, then "
            "R_plus^mu=0 and R_minus^mu=0 for the Lorentz dust transport branch."
        ),
        "proved_as_algebraic_implication": True,
        "source_derived": False,
    }
    positive_chain = [
        "R_plus^mu = D_plus T_plus + B_plus[u D_minus(rho_minus u) + rho_minus u D_minus u + C rho_minus u u]",
        "assume D_plus T_plus=0",
        "assume D_minus(rho_minus u)=0",
        "assume u D_minus u + C u u=0",
        "therefore R_plus^mu=0",
    ]
    negative_chain = [
        "R_minus^mu = D_minus T_minus + B_minus[u D_plus(rho_plus u) + rho_plus u D_plus u - C rho_plus u u]",
        "assume D_minus T_minus=0",
        "assume D_plus(rho_plus u)=0",
        "assume u D_plus u - C u u=0",
        "therefore R_minus^mu=0",
    ]
    remaining_physical_work = [
        "derive the transported continuity assumptions from Janus source equations",
        "derive the transported force assumptions from Janus source equations",
        "derive L_minus_to_plus/L_plus_to_minus used in the transported velocities",
        "prove the same L maps induce Q_cross and K_plus/K_minus consistently",
        "extend beyond dust if pressure or anisotropic stress is required",
    ]
    return {
        "description": "Conditional algebraic closure theorem for the Lorentz dust Bianchi branch.",
        "status": "conditional-theorem",
        "conditional_closure_proved": True,
        "conditions_source_derived": False,
        "residuals_physically_closed": False,
        "physics_closed": False,
        "prediction_ready": False,
        "theorem": theorem,
        "positive_chain": positive_chain,
        "negative_chain": negative_chain,
        "remaining_physical_work": remaining_physical_work,
        "verdict": (
            "The algebraic implication is closed: the listed assumptions imply both "
            "residuals vanish in the Lorentz dust branch. The physical proof remains "
            "open until those assumptions are derived from Janus equations."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# Bianchi Conditional Closure Theorem",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Conditional closure proved: {payload['conditional_closure_proved']}",
        f"Conditions source-derived: {payload['conditions_source_derived']}",
        f"Residuals physically closed: {payload['residuals_physically_closed']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Theorem",
        "",
        f"- `{payload['theorem']['name']}`",
        f"- {payload['theorem']['claim']}",
        "",
        "## Positive Chain",
        "",
    ]
    lines.extend(f"- `{item}`" for item in payload["positive_chain"])
    lines.extend(["", "## Negative Chain", ""])
    lines.extend(f"- `{item}`" for item in payload["negative_chain"])
    lines.extend(["", "## Remaining Physical Work", ""])
    lines.extend(f"- {item}" for item in payload["remaining_physical_work"])
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
