from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/qcross_flrw_comoving_tetrad_branch.md")
JSON_PATH = Path("outputs/reports/qcross_flrw_comoving_tetrad_branch.json")


def build_payload() -> dict:
    setup = [
        "ds_s^2=-N_s(t)^2 dt^2 + a_s(t)^2 gamma_ij dx^i dx^j",
        "theta_s^0=N_s dt",
        "theta_s^i=a_s sigma^i",
        "eta_AB=diag(-1,1,1,1)",
        "u_plus^A=u_minus^A=(1,0,0,0) for comoving fluids",
        "k_plus^A=E(1,n) in the positive tetrad, with |n|=1",
    ]
    map_branch = {
        "name": "aligned_comoving_tetrads",
        "map": "L_minus_to_plus^A_B = delta^A_B",
        "transported_velocity": "u_minus_to_plus^A=(1,0,0,0)",
        "positive_projection": "A_plus=(eta_AB u_plus^A k_plus^B)^2=E^2",
        "negative_projection": "A_minus=(eta_AB u_minus_to_plus^A k_plus^B)^2=E^2",
        "result": "Q_cross=A_minus/A_plus=1",
    }
    assumptions = [
        "same event identification between sectors",
        "aligned time orientation and spatial triads",
        "no relative boost, rotation, vorticity, or peculiar velocity",
        "positive photons are always evaluated in the positive tetrad",
        "Q_det determinant/volume factors are not part of L_minus_to_plus",
    ]
    warnings = [
        "coordinate covector comparison can produce raw (N_minus/N_plus)^2 lapse powers; that is not this tetrad branch",
        "with conformal lapses N_s=a_s, the raw coordinate warning path gives (a_minus/a_plus)^2",
        "pressure changes the stress contraction rho -> rho+p, not the comoving Q_cross value",
        "anisotropic stress adds Pi_kk and is outside this scalar branch",
        "perturbations require a nontrivial L_minus_to_plus map",
    ]
    return {
        "description": "Closed FLRW comoving tetrad branch for Q_cross.",
        "status": "closed-special-branch",
        "branch_closed": True,
        "physics_closed": False,
        "setup": setup,
        "map_branch": map_branch,
        "assumptions": assumptions,
        "warnings": warnings,
        "verdict": (
            "Under aligned comoving FLRW tetrads, Q_cross=1 follows from the "
            "orthonormal projection itself. This closes only that branch; the "
            "global or perturbed L_minus_to_plus map remains open."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# Q_cross FLRW Comoving Tetrad Branch",
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
    lines.extend(["", "## Map Branch", ""])
    for key, value in payload["map_branch"].items():
        lines.append(f"- `{key}`: `{value}`")
    lines.extend(["", "## Assumptions", ""])
    lines.extend(f"- {item}" for item in payload["assumptions"])
    lines.extend(["", "## Warnings", ""])
    lines.extend(f"- {item}" for item in payload["warnings"])
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
