from __future__ import annotations

from pathlib import Path
import json
import sys


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_orbifold_pt_soldering_candidate import build_payload as build_orbifold


REPORT_PATH = Path("outputs/reports/p0_orbifold_pt_action_variation_gate.md")
JSON_PATH = Path("outputs/reports/p0_orbifold_pt_action_variation_gate.json")


def build_payload() -> dict:
    orbifold = build_orbifold()
    action_terms = [
        {
            "term": "sector_einstein_hilbert",
            "density": "sqrt(-g_plus) R_plus + sqrt(-g_minus) R_minus",
            "role": "keeps Janus sector dynamics before cross solder variation",
            "source_status": "standard sector scaffold",
        },
        {
            "term": "solder_yang_mills",
            "density": "sqrt(-g_orb) Tr(F_PT wedge *F_PT)",
            "role": "gives A_PT Euler equation and holonomy dynamics",
            "source_status": "new orbifold extension candidate",
        },
        {
            "term": "defect_boundary",
            "density": "Integral_{Sigma_PT} B(g_plus,g_minus,A_PT,tau)",
            "role": "supplies PT fixed-locus boundary and matching data",
            "source_status": "not derived",
        },
        {
            "term": "matter_solder_coupling",
            "density": "J_matter(T_plus,L_gamma T_minus L_gamma^T,A_PT)",
            "role": "ties K_plus/K_minus, Q_cross and Vlasov to the same holonomy",
            "source_status": "not derived",
        },
    ]
    variation_rows = [
        {
            "variation": "delta_A_PT",
            "formal_equation": "D_A *F_PT = J_defect + J_matter",
            "derived_formally": True,
            "closed_for_prediction": False,
            "blocker": "J_defect/J_matter candidates are triaged separately and not source-derived",
        },
        {
            "variation": "delta_g_plus",
            "formal_equation": "G_plus = T_plus + K_plus[A_PT,F_PT,B]",
            "derived_formally": True,
            "closed_for_prediction": False,
            "blocker": "K_plus tensor variation not computed from accepted action",
        },
        {
            "variation": "delta_g_minus",
            "formal_equation": "G_minus = T_minus + K_minus[A_PT,F_PT,B]",
            "derived_formally": True,
            "closed_for_prediction": False,
            "blocker": "K_minus mirror tensor variation not computed from accepted action",
        },
        {
            "variation": "delta_boundary_Sigma_PT",
            "formal_equation": "n_A *F_PT + delta B/delta A_PT = 0 on Sigma_PT",
            "derived_formally": True,
            "closed_for_prediction": False,
            "blocker": "Sigma_PT dynamics and boundary functional B are not fixed",
        },
        {
            "variation": "orbifold_noether",
            "formal_equation": "delta_xi S_orb = combined Noether identity",
            "derived_formally": True,
            "closed_for_prediction": False,
            "blocker": "must split into R_plus=0 and R_minus=0, not only combined covariance",
        },
    ]
    induced_quantities = [
        {
            "quantity": "same_L",
            "definition": "L_gamma = P exp integral_gamma A_PT",
            "status": "structural-if-A_PT-unique",
        },
        {
            "quantity": "S_path",
            "definition": "path action induced by A_PT holonomy/defect boundary",
            "status": "formal-induced-not-closed",
        },
        {
            "quantity": "C_J/V_J",
            "definition": "coefficients from Tr(F_PT^2), defect terms and matter solder couplings",
            "status": "not coefficient-closed",
        },
    ]
    return {
        "description": (
            "Candidate orbifold/PT action and variation gate. It writes the minimal "
            "action skeleton needed to make A_PT, same-L and S_path dynamical."
        ),
        "status": "orbifold-pt-action-variation-gate-open",
        "depends_on": ["p0_orbifold_pt_soldering_candidate"],
        "orbifold_candidate_status": orbifold["status"],
        "action_object": "S_orb[g_plus,g_minus,A_PT,tau,Sigma_PT,matter]",
        "action_terms": action_terms,
        "variation_rows": variation_rows,
        "induced_quantities": induced_quantities,
        "orbifold_action_written": True,
        "a_pt_euler_equation_written": True,
        "a_pt_euler_equation_derived_from_accepted_source": False,
        "same_l_structural_if_unique_connection": True,
        "cj_vj_coefficients_derived": False,
        "defect_boundary_law_derived": False,
        "k_plus_k_minus_derived": False,
        "split_noether_bianchi_proved": False,
        "ghost_stability_closed": False,
        "uses_observational_fit": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "The orbifold action skeleton is now explicit and gives the formal "
            "A_PT equation D_A*F=J. It is not accepted physics until J_defect, "
            "matter solder coupling, boundary law, metric variations, split "
            "Noether and stability are derived."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Orbifold/PT Action Variation Gate",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Action object: `{payload['action_object']}`",
        f"Orbifold action written: {payload['orbifold_action_written']}",
        f"A_PT Euler equation written: {payload['a_pt_euler_equation_written']}",
        (
            "A_PT Euler equation derived from accepted source: "
            f"{payload['a_pt_euler_equation_derived_from_accepted_source']}"
        ),
        f"Same-L structural if unique connection: {payload['same_l_structural_if_unique_connection']}",
        f"C_J/V_J coefficients derived: {payload['cj_vj_coefficients_derived']}",
        f"Defect boundary law derived: {payload['defect_boundary_law_derived']}",
        f"K_plus/K_minus derived: {payload['k_plus_k_minus_derived']}",
        f"Split Noether/Bianchi proved: {payload['split_noether_bianchi_proved']}",
        f"Ghost stability closed: {payload['ghost_stability_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Action Terms",
        "",
        "| term | density | role | source status |",
        "|---|---|---|---|",
    ]
    for row in payload["action_terms"]:
        lines.append(f"| {row['term']} | `{row['density']}` | {row['role']} | {row['source_status']} |")
    lines.extend(["", "## Variations", "", "| variation | formal equation | formal | closed | blocker |", "|---|---|---:|---:|---|"])
    for row in payload["variation_rows"]:
        lines.append(
            f"| {row['variation']} | `{row['formal_equation']}` | "
            f"{row['derived_formally']} | {row['closed_for_prediction']} | {row['blocker']} |"
        )
    lines.extend(["", "## Induced Quantities", ""])
    lines.extend(
        f"- `{row['quantity']}` = `{row['definition']}` ({row['status']})"
        for row in payload["induced_quantities"]
    )
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
