from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_janus_transport_residual_derivation.md")
JSON_PATH = Path("outputs/reports/p0_janus_transport_residual_derivation.json")


def build_payload() -> dict:
    janus_bianchi_start = [
        "G_plus^{mu nu}=chi_plus(T_plus^{mu nu}+B_plus K_plus^{mu nu})",
        "G_minus^{mu nu}=chi_minus(B_minus K_minus^{mu nu}+T_minus^{mu nu})",
        "D_plus_nu G_plus^{mu nu}=0 -> R_plus^mu=D_plus_nu(T_plus^{mu nu}+B_plus K_plus^{mu nu})=0",
        "D_minus_nu G_minus^{mu nu}=0 -> R_minus^mu=D_minus_nu(B_minus K_minus^{mu nu}+T_minus^{mu nu})=0",
    ]
    l_transport_definition = [
        "u_-to+^A=L_minus_to_plus^A_B u_-^B",
        "u_+to-^A=L_plus_to_minus^A_B u_+^B",
        "L_minus_to_plus^T eta L_minus_to_plus=eta",
        "L_plus_to_minus^T eta L_plus_to_minus=eta",
        "L_plus_to_minus=L_minus_to_plus^{-1} or a source-derived mirror map",
    ]
    induced_k_definition = [
        "K_plus^{AB}=rho_minus u_-to+^A u_-to+^B for dust",
        "K_minus^{AB}=rho_plus u_+to-^A u_+to-^B for dust",
        "perfect-fluid extension must add transported p eta^{AB} and projector terms",
        "anisotropic extension must add transported Pi^{AB}",
    ]
    qcross_definition = [
        "Q_cross_plus=(eta_AB u_-to+^A k_plus^B)^2/(eta_AB u_plus^A k_plus^B)^2",
        "Q_cross_minus=(eta_AB u_+to-^A k_minus^B)^2/(eta_AB u_minus^A k_minus^B)^2",
        "the same L maps used in K_plus/K_minus must define u_-to+ and u_+to-",
    ]
    residual_reduction = [
        {
            "sector": "plus",
            "residual": "R_plus^A",
            "after_same_sector_conservation": "D_plus_B(B_plus K_plus^{AB})",
            "dust_reduction": (
                "B_plus[(D_minus_B(rho_minus u_-to+^B))u_-to+^A "
                "+ rho_minus u_-to+^B(D_minus_B u_-to+^A + C^A_{BC}u_-to+^C)] "
                "+ density_measure_terms"
            ),
            "vanishes_if": [
                "transported negative continuity holds",
                "transported negative receiver-force equation holds",
                "B_plus density-measure terms match Q_det convention",
                "D L_minus_to_plus terms are included in the force equation",
            ],
        },
        {
            "sector": "minus",
            "residual": "R_minus^A",
            "after_same_sector_conservation": "D_minus_B(B_minus K_minus^{AB})",
            "dust_reduction": (
                "B_minus[(D_plus_B(rho_plus u_+to-^B))u_+to-^A "
                "+ rho_plus u_+to-^B(D_plus_B u_+to-^A - C^A_{BC}u_+to-^C)] "
                "+ density_measure_terms"
            ),
            "vanishes_if": [
                "transported positive continuity holds",
                "transported positive receiver-force equation holds",
                "B_minus density-measure terms match Q_det convention",
                "D L_plus_to_minus terms are included in the force equation",
            ],
        },
    ]
    source_equations_needed = [
        "Janus field equations must specify B_plus and B_minus density weights",
        "Janus source equations must imply transported continuity in both directions",
        "Janus geodesic/transport equations must imply receiver-force equations in both directions",
        "Janus must supply or constrain D_alpha L_minus_to_plus and D_alpha L_plus_to_minus",
        "the optical sector must use the same L as the stress transport sector",
    ]
    closed_now = [
        "Bianchi identities reduce the problem to R_plus=0 and R_minus=0",
        "K_plus/K_minus and Q_cross are tied to one Lorentz/tetrad L structure",
        "dust residuals reduce to continuity, receiver-force, D L, and density-measure terms",
        "scalar Q_det/Q_cross absorption is excluded",
    ]
    still_open = [
        "published/source-derived equations for D L are not inserted",
        "density-measure convention B_plus/B_minus is not fixed as a proven Q_det",
        "pressure and Pi tensor transport are not reduced to zero residuals",
        "there is no prediction until both residual rows vanish from source equations",
    ]
    return {
        "description": "P0 derivation reducing Janus Bianchi identities to the L/K/Q_cross transport residual obligations.",
        "status": "source-reduction-derived-open",
        "janus_bianchi_reduction_done": True,
        "single_l_structure_required": True,
        "k_and_qcross_linked": True,
        "dust_residual_reduction_done": True,
        "source_equations_inserted": False,
        "r_plus_closed": False,
        "r_minus_closed": False,
        "physics_closed": False,
        "prediction_ready": False,
        "janus_bianchi_start": janus_bianchi_start,
        "l_transport_definition": l_transport_definition,
        "induced_k_definition": induced_k_definition,
        "qcross_definition": qcross_definition,
        "residual_reduction": residual_reduction,
        "source_equations_needed": source_equations_needed,
        "closed_now": closed_now,
        "still_open": still_open,
        "verdict": (
            "The Janus Bianchi identities force R_plus=R_minus=0 and reduce the "
            "dust transport branch to explicit L/K/Q_cross obligations. This is a "
            "derivation of the residual structure, not yet a physical closure, "
            "because the source-derived D L and density-measure equations remain open."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Janus Transport Residual Derivation",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Janus Bianchi reduction done: {payload['janus_bianchi_reduction_done']}",
        f"Single L structure required: {payload['single_l_structure_required']}",
        f"K and Q_cross linked: {payload['k_and_qcross_linked']}",
        f"Dust residual reduction done: {payload['dust_residual_reduction_done']}",
        f"Source equations inserted: {payload['source_equations_inserted']}",
        f"R_plus closed: {payload['r_plus_closed']}",
        f"R_minus closed: {payload['r_minus_closed']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Janus Bianchi Start",
        "",
    ]
    lines.extend(f"- `{item}`" for item in payload["janus_bianchi_start"])
    lines.extend(["", "## L Transport Definition", ""])
    lines.extend(f"- `{item}`" for item in payload["l_transport_definition"])
    lines.extend(["", "## Induced K Definition", ""])
    lines.extend(f"- `{item}`" for item in payload["induced_k_definition"])
    lines.extend(["", "## Q_cross Definition", ""])
    lines.extend(f"- `{item}`" for item in payload["qcross_definition"])
    lines.extend(["", "## Residual Reduction", ""])
    for row in payload["residual_reduction"]:
        lines.append(f"- {row['sector']}: `{row['residual']}`")
        lines.append(f"  - after conservation: `{row['after_same_sector_conservation']}`")
        lines.append(f"  - dust reduction: `{row['dust_reduction']}`")
        lines.extend(f"  - vanishes if {item}" for item in row["vanishes_if"])
    lines.extend(["", "## Source Equations Needed", ""])
    lines.extend(f"- {item}" for item in payload["source_equations_needed"])
    lines.extend(["", "## Closed Now", ""])
    lines.extend(f"- {item}" for item in payload["closed_now"])
    lines.extend(["", "## Still Open", ""])
    lines.extend(f"- {item}" for item in payload["still_open"])
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
