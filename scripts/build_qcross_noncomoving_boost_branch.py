from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/qcross_noncomoving_boost_branch.md")
JSON_PATH = Path("outputs/reports/qcross_noncomoving_boost_branch.json")


def build_payload() -> dict:
    setup = [
        "positive tetrad frame with eta_AB=diag(-1,1,1,1)",
        "k_plus^A=E(1,n), |n|=1",
        "u_minus_to_plus^A=gamma(1,beta_vec)",
        "gamma=(1-|beta_vec|^2)^-1/2",
    ]
    result = {
        "projection_plus": "A_plus=E^2 for u_plus^A=(1,0,0,0)",
        "projection_minus": "A_minus=E^2 gamma^2(1-beta_vec.n)^2",
        "q_cross": "Q_cross=gamma^2(1-beta_vec.n)^2",
        "small_beta_order2": "Q_cross=1-2 beta_parallel+|beta|^2+beta_parallel^2+O(beta^3)",
    }
    rotation_role = [
        "a pure spatial rotation of the tetrad does not change Q_cross for comoving u_minus",
        "rotation matters only through the components of beta_vec relative to n",
        "Q_cross=gamma^2[1-(R beta_minus).n_plus]^2=gamma^2[1-beta_minus.(R^T n_plus)]^2",
        "the scalar beta_vec.n is the invariant local directional input in this branch",
    ]
    requirements = [
        "beta_vec must be derived from Janus dynamics or a declared physical velocity field",
        "the boost map is Lorentz-admissible: L^T eta L=eta",
        "Q_det remains outside the boost map",
        "Bianchi compatibility still has to be checked for K_plus/K_minus transport",
    ]
    return {
        "description": "Closed local non-comoving Lorentz-boost branch for Q_cross.",
        "status": "closed-local-branch",
        "branch_closed": True,
        "physics_closed": False,
        "setup": setup,
        "result": result,
        "rotation_role": rotation_role,
        "requirements": requirements,
        "verdict": (
            "The non-comoving local Lorentz branch gives the implemented velocity "
            "formula exactly. It becomes physical only when beta_vec is source-derived "
            "and the map is connected to Bianchi-compatible stress transport."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# Q_cross Non-Comoving Boost Branch",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Branch closed: {payload['branch_closed']}",
        f"Physics closed: {payload['physics_closed']}",
        "",
        "## Setup",
        "",
    ]
    lines.extend(f"- `{item}`" for item in payload["setup"])
    lines.extend(["", "## Result", ""])
    for key, value in payload["result"].items():
        lines.append(f"- `{key}`: `{value}`")
    lines.extend(["", "## Rotation Role", ""])
    lines.extend(f"- {item}" for item in payload["rotation_role"])
    lines.extend(["", "## Requirements", ""])
    lines.extend(f"- {item}" for item in payload["requirements"])
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
