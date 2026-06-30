from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_eft_active_stress_alpha_derivation.md")
JSON_PATH = Path("outputs/reports/p0_eft_active_stress_alpha_derivation.json")


def build_payload() -> dict:
    contorsion = {
        "source": "Janus radion/tetrad soldering gradients and Pin torsion components",
        "quadratic_terms": "T_eff_torsion contains q_T^2, q_A^2, and mixed boundary response terms",
        "spinless_limit": "no direct spin force, but torsion stress can enter geometry as effective active source",
        "open_tensor": "exact contractions depend on the contorsion ansatz already fixed at the boundary",
    }
    alpha = {
        "definition": "alpha_Janus(a) = ratio of torsion/bridge active stress response to rho_crit(a)",
        "poisson_form": "k^2 Phi = -4*pi*G*a^2*mu(k,a)*rho*delta",
        "mu_form": "1+alpha_Janus(a)*k^2/(k^2+3H(a)^2/2)",
        "pi_dependency": "anisotropic stress Pi contributes to slip/lensing and may feed alpha",
    }
    theorem_status = {
        "active_stress_definition_encoded": True,
        "contorsion_quadratic_source_identified": True,
        "alpha_definition_encoded": True,
        "poisson_mu_form_linked": True,
        "contorsion_contractions_computed": False,
        "pi_moment_closed": False,
        "alpha_Janus_derived": False,
        "prediction_ready_unconditional": False,
    }
    obligations = [
        "compute contorsion contractions q_T^2/q_A^2 in T_eff_torsion",
        "compute Pi from transported spinless distribution or impose isotropy as a conditional branch",
        "derive alpha_Janus(a) from the active stress ratio without fitting",
    ]
    return {
        "description": "Active stress tensor derivation target for alpha_Janus(a).",
        "status": "alpha-definition-ready-contorsion-pi-open",
        "contorsion": contorsion,
        "alpha": alpha,
        "theorem_status": theorem_status,
        "obligations": obligations,
        "verdict": (
            "alpha_Janus(a) is now defined as an active-stress ratio. It is not derived until "
            "the contorsion contractions and Pi moment are computed."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 EFT Active Stress Alpha Derivation",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        "",
        "## Contorsion",
    ]
    lines.extend(f"- {key}: {value}" for key, value in payload["contorsion"].items())
    lines.extend(["", "## Alpha"])
    lines.extend(f"- {key}: {value}" for key, value in payload["alpha"].items())
    lines.extend(["", "## Status"])
    lines.extend(f"- {key}: {value}" for key, value in payload["theorem_status"].items())
    lines.extend(["", "## Obligations"])
    lines.extend(f"- {item}" for item in payload["obligations"])
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
