from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_l_transport_candidate_geometry.md")
JSON_PATH = Path("outputs/reports/p0_l_transport_candidate_geometry.json")


def build_payload() -> dict:
    candidates = [
        {
            "name": "raw_tetrad_solder",
            "definition": "L_geom^A_B=e_plus^A_mu E_minus^mu_B",
            "dl_formula_or_unknowns": (
                "D_alpha L_geom^A_B=(D_alpha e_plus^A_mu)E_minus^mu_B+"
                "e_plus^A_mu(D_alpha E_minus^mu_B); computable from the two spin "
                "connections after the derivative convention is fixed"
            ),
            "lorentz_admissibility": (
                "not admissible unless L_geom^T eta L_geom=eta is proved on the branch"
            ),
            "janus_source_derived": False,
            "bianchi_qcross_usability": (
                "bookkeeping only; can audit candidate DL terms but cannot be used as "
                "optical Q_cross or Bianchi K transport without the Lorentz proof"
            ),
        },
        {
            "name": "lorentz_polar_projected_map",
            "definition": "L_Lorentz=polar_eta(L_geom)",
            "dl_formula_or_unknowns": (
                "D_alpha L_Lorentz requires differentiating the eta-polar projection; "
                "unknown projection branch, regularity, and source equation for D L"
            ),
            "lorentz_admissibility": "admissible by construction where polar_eta is defined",
            "janus_source_derived": False,
            "bianchi_qcross_usability": (
                "usable algebraically for Q_cross after branch choices, but not a "
                "Bianchi closure law until its DL is source-derived"
            ),
        },
        {
            "name": "local_boost_from_relative_velocity",
            "definition": "L_boost(u_minus,u_plus)=standard proper Lorentz boost between local four-velocities",
            "dl_formula_or_unknowns": (
                "D_alpha L_boost follows from D_alpha u_minus, D_alpha u_plus, gamma, "
                "and boost direction derivatives; requires equations of motion and "
                "nonzero relative-velocity branch control"
            ),
            "lorentz_admissibility": "admissible on timelike, time-oriented velocity branches",
            "janus_source_derived": False,
            "bianchi_qcross_usability": (
                "candidate for optical Q_cross on velocity branches; insufficient for "
                "Bianchi K transport unless Janus sources force this boost law"
            ),
        },
        {
            "name": "source_transport_law",
            "definition": "D_alpha L^A_B=F^A_{B alpha}[g_plus,g_minus,C,T_plus,T_minus]",
            "dl_formula_or_unknowns": (
                "unknown F must be derived from Janus coupled field/source equations "
                "and must include the mirror plus-to-minus law"
            ),
            "lorentz_admissibility": (
                "requires F to preserve D_alpha(L^T eta L)=0 and initial Lorentz data"
            ),
            "janus_source_derived": "target-not-yet",
            "bianchi_qcross_usability": (
                "the only candidate capable of closing Bianchi residuals and Q_cross "
                "together once F, Lorentz preservation, and mirror consistency are proved"
            ),
        },
    ]
    return {
        "description": "Bounded P0 research artifact comparing candidate L/DL geometry definitions.",
        "status": "research-artifact",
        "prediction_ready": False,
        "candidates": candidates,
        "required_next_proofs": [
            "prove or reject L_geom^T eta L_geom=eta before using raw L_geom as admissible transport",
            "derive any accepted D L law from Janus source equations, not from fitting observables",
            "show the same L law induces Bianchi K transport and optical Q_cross",
            "prove residual closure R_plus=0 and R_minus=0 before prediction claims",
        ],
        "verdict": (
            "L_geom gives a computable DL through spin connections, but it is not "
            "admissible unless the Lorentz condition is proved. The source-transport "
            "law is the only structurally complete route, but its F is still unknown."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 L-Transport Candidate Geometry",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Candidates",
        "",
    ]
    for candidate in payload["candidates"]:
        lines.extend(
            [
                f"### {candidate['name']}",
                "",
                f"- Definition: `{candidate['definition']}`",
                f"- DL formula/unknowns: {candidate['dl_formula_or_unknowns']}",
                f"- Lorentz admissibility: {candidate['lorentz_admissibility']}",
                f"- Janus-source-derived: {candidate['janus_source_derived']}",
                f"- Bianchi/Q_cross usability: {candidate['bianchi_qcross_usability']}",
                "",
            ]
        )
    lines.extend(["## Required Next Proofs", ""])
    lines.extend(f"- {item}" for item in payload["required_next_proofs"])
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
