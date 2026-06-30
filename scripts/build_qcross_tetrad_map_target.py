from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/qcross_tetrad_map_target.md")
JSON_PATH = Path("outputs/reports/qcross_tetrad_map_target.json")


def build_payload() -> dict:
    definitions = {
        "positive_photon_frame": "k_plus^A = e_plus^A_mu k_plus^mu",
        "positive_velocity_frame": "u_plus^A = e_plus^A_mu u_plus^mu",
        "raw_geometric_solder_map": "L_geom_minus_to_plus^A_B=e_plus^A_mu E_minus_B^mu",
        "transported_negative_velocity": "u_minus_to_plus^A = L_minus_to_plus^A_B u_minus^B",
        "positive_projection": "A_plus = (eta_AB u_plus^A k_plus^B)^2",
        "negative_projection": "A_minus = (eta_AB u_minus_to_plus^A k_plus^B)^2",
        "q_cross": "Q_cross = A_minus / A_plus",
    }
    map_requirements = [
        "e_plus and e_minus are tetrads at the same event after a declared sector identification",
        "raw L_geom=e_plus E_minus must be audited through L_geom^T eta L_geom - eta",
        "admissible optical L_minus_to_plus must preserve eta_AB",
        "L_minus_to_plus must be time-orientation preserving",
        "k_plus is always the positive-sector null direction",
        "Q_det density/volume factors are not part of L_minus_to_plus",
    ]
    reductions = [
        {
            "case": "flrw_aligned_comoving_tetrads",
            "condition": "u_plus^A=u_minus^A=(1,0,0,0), k_plus^A=E(1,n), L_minus_to_plus=I",
            "result": "Q_cross=1",
        },
        {
            "case": "raw_geometric_solder_map",
            "condition": "L_geom=e_plus E_minus before Lorentz compatibility is imposed",
            "result": "gauge/metric-comparison warning, not final Q_cross",
        },
        {
            "case": "identity_frame_map",
            "condition": "L_minus_to_plus=I and u_plus=(1,0,0,0)",
            "result": "Q_cross=gamma_minus^2(1-beta_vec.n)^2",
        },
        {
            "case": "equal_projection",
            "condition": "eta(u_minus_to_plus,k_plus)^2=eta(u_plus,k_plus)^2",
            "result": "Q_cross=1",
        },
    ]
    blockers = [
        "derive L_minus_to_plus from Janus coupled metrics, not from lensing data",
        "do not identify raw L_geom with admissible optical L_minus_to_plus unless Lorentz compatibility is proved",
        "nontrivial L_minus_to_plus must induce M_minus_to_plus used in K_plus transport",
        "mirror M_plus_to_minus/K_minus branch and both residuals R_plus/R_minus must be checked",
        "extend the closed FLRW comoving branch to perturbed/non-comoving sectors",
        "connect this local tetrad map to the global Bianchi K_plus/K_minus transport",
        "derive a source-backed negative-sector velocity field before PM use becomes physical",
        "keep pressure and anisotropic stress contractions outside the dust-only reduction",
    ]
    return {
        "description": "Tetrad-map target for the Janus Q_cross optical projection.",
        "status": "map-target",
        "physics_closed": False,
        "definitions": definitions,
        "map_requirements": map_requirements,
        "reductions": reductions,
        "blockers": blockers,
        "verdict": (
            "Q_cross is reduced to a local Lorentz-frame transport problem. The "
            "implemented velocity formula is recovered only when the frame map is "
            "declared; the Janus-derived L_minus_to_plus map remains open."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# Q_cross Tetrad Map Target",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Physics closed: {payload['physics_closed']}",
        "",
        "## Definitions",
        "",
    ]
    for key, value in payload["definitions"].items():
        lines.append(f"- `{key}`: `{value}`")
    lines.extend(["", "## Map Requirements", ""])
    lines.extend(f"- {item}" for item in payload["map_requirements"])
    lines.extend(["", "## Reductions", ""])
    lines.extend(["| case | condition | result |", "|---|---|---|"])
    for row in payload["reductions"]:
        lines.append(f"| {row['case']} | `{row['condition']}` | `{row['result']}` |")
    lines.extend(["", "## Blockers", ""])
    lines.extend(f"- {item}" for item in payload["blockers"])
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
