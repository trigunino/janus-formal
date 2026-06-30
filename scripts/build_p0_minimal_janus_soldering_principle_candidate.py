from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_minimal_janus_soldering_principle_candidate.md")
JSON_PATH = Path("outputs/reports/p0_minimal_janus_soldering_principle_candidate.json")


def build_payload() -> dict:
    fields = [
        "two sectors (M_plus,g_plus,nabla_plus,e_plus) and (M_minus,g_minus,nabla_minus,e_minus)",
        "diffeomorphism phi_minus_to_plus with inverse phi_plus_to_minus",
        "Lorentz/tetrad solder L_minus_to_plus and inverse L_plus_to_minus",
        "Jacobian J_phi=det(D phi) and matter measure B_4vol=J_phi*S_slice",
        "relative connection Omega=L^{-1} D L",
    ]
    candidate_equations = [
        "phi_plus_to_minus(phi_minus_to_plus(x))=x and phi_minus_to_plus(phi_plus_to_minus(y))=y",
        "L_plus_to_minus=L_minus_to_plus^{-1}",
        "eta_cd L^c_a L^d_b=eta_ab",
        "phi^* theta_minus^a = L^a_b theta_plus^b",
        "Omega = L^{-1}(phi^* omega_minus L - L omega_plus + dL)",
        "D Omega + Omega wedge Omega = phi^* R_minus - R_plus + S_relative",
        "B_4vol=J_phi*S_slice with S_slice fixed by the same lapse/slice rule",
    ]
    acceptance_tests = [
        "S_relative must be derived from Janus field equations or an accepted action, not fitted",
        "the same L must feed K_plus, mirror K_minus, Q_cross, optics and Vlasov transport",
        "split Noether identities must force R_plus=0 and R_minus=0 separately",
        "B_4vol must be compatible with the selected phi/lapse/slice, not used to hide J_phi freedom",
        "Q_det/Q_cross scalar absorption is forbidden",
        "FLRW/comoving simplifications cannot be promoted to general perturbations",
    ]
    blockers = [
        "no current workspace artifact derives S_relative from a published Janus source",
        "pure-gauge L is path-independent but may erase physical relative curvature",
        "Lorentz compatibility alone leaves rapidity and D L unselected",
        "B_4vol fixes only a product unless lapse/slice/gauge are also selected",
        "pressure, Pi and kinetic moments still need a same-L matter law",
    ]
    return {
        "description": "Minimal Janus soldering principle candidate for selecting phi/J/L without observational fit.",
        "status": "new-principle-candidate-not-source-derived",
        "new_axiom_candidate": True,
        "source_derived": False,
        "zero_rustine_if_source_derived": True,
        "prediction_ready": False,
        "fields": fields,
        "candidate_equations": candidate_equations,
        "acceptance_tests": acceptance_tests,
        "blockers": blockers,
        "verdict": (
            "This is the clean missing geometry: a covariant solder between the plus and "
            "minus sectors. It is not yet a proof. It becomes zero-rustine only if "
            "S_relative and the lapse/slice rule are derived from Janus source/action data."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Minimal Janus Soldering Principle Candidate",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"New axiom candidate: {payload['new_axiom_candidate']}",
        f"Source derived: {payload['source_derived']}",
        f"Zero-rustine if source derived: {payload['zero_rustine_if_source_derived']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Fields",
        "",
    ]
    lines.extend(f"- `{item}`" for item in payload["fields"])
    lines.extend(["", "## Candidate Equations", ""])
    lines.extend(f"- `{item}`" for item in payload["candidate_equations"])
    lines.extend(["", "## Acceptance Tests", ""])
    lines.extend(f"- {item}" for item in payload["acceptance_tests"])
    lines.extend(["", "## Blockers", ""])
    lines.extend(f"- {item}" for item in payload["blockers"])
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
