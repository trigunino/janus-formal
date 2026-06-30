from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_eft_global_boundary_spectral_convergence.md")
JSON_PATH = Path("outputs/reports/p0_eft_global_boundary_spectral_convergence.json")


def build_payload() -> dict:
    run1 = {
        "lambda": "lambda=-4*q_T from oriented volume/solder Palatini variation",
        "kappa": "kappa=2*q_A*Delta_chi from Nieh-Yan/Pin axial boundary variation",
        "beta": "beta*Delta_chi=-sigma*(1+tau)/2 as Cartan-GHY boundary response",
        "boundary_factorization": "M_tot=gamma^n(I +/- gamma^n gamma5)",
        "local_projector": "P_chiral psi|_Sigma=0",
        "status": "closed conditionally",
    }
    run2 = {
        "aps_operator": "A_APS=gamma^n D_Sigma",
        "commutation": "[A_APS,gamma5]=0 under the Janus boundary Clifford assumptions",
        "zero_modes": "ker(A_APS)=0 on compact Riemannian APS boundary with R_Sigma=6H^2>0",
        "eta_mod2": "0 conditionally",
        "status": "closed conditionally",
    }
    theorem_status = {
        "beta_response_ratio_accepted": True,
        "run1_conditionally_closed": True,
        "run2_conditionally_closed": True,
        "aps_domain_conditionally_invariant": True,
        "eta_mod2_conditionally_zero": True,
        "prediction_ready_conditional": True,
        "prediction_ready_unconditional": False,
    }
    conditions = [
        "boundary is the compact Riemannian APS boundary used by the eta invariant",
        "Janus normal/orientation conventions are fixed as in lambda closure",
        "beta is accepted as a Cartan-GHY response ratio, not a standalone constant",
        "Pin- axial normalization fixes q_A and Nieh-Yan normalization fixes kappa",
    ]
    return {
        "description": "Global convergence of boundary RUN 1 and spectral RUN 2 for the Janus EFT route.",
        "status": "prediction-ready-conditional-not-unconditional",
        "run1": run1,
        "run2": run2,
        "theorem_status": theorem_status,
        "conditions": conditions,
        "verdict": (
            "The boundary/spectral sector is closed conditionally. It is not unconditional: "
            "it depends on the APS Riemannian boundary, orientation conventions, Pin- axial "
            "normalization, and beta as a response ratio."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 EFT Global Boundary Spectral Convergence",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        "",
        "## RUN 1",
    ]
    lines.extend(f"- {key}: {value}" for key, value in payload["run1"].items())
    lines.extend(["", "## RUN 2"])
    lines.extend(f"- {key}: {value}" for key, value in payload["run2"].items())
    lines.extend(["", "## Status"])
    lines.extend(f"- {key}: {value}" for key, value in payload["theorem_status"].items())
    lines.extend(["", "## Conditions"])
    lines.extend(f"- {item}" for item in payload["conditions"])
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
