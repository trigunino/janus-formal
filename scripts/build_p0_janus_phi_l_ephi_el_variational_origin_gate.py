from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_janus_phi_l_ephi_el_variational_origin_gate.md")
JSON_PATH = Path("outputs/reports/p0_janus_phi_l_ephi_el_variational_origin_gate.json")


def build_payload() -> dict:
    derive_from = [
        "Janus cross-source action or source functional containing the map phi",
        "matter pullback action with B_4vol/J_phi measure response",
        "same-L tetrad transport stack used by K, Q_cross and Vlasov",
        "mirror inverse constraint phi_minus=phi_plus^{-1}, L_minus=L_plus^{-1}",
    ]
    not_derive_from = [
        "survey residuals or observational fitting",
        "scalar Q_cross/Q_det absorption",
        "independent L choices for K, Q_cross and matter transport",
        "a hand-selected gauge/lapse/slice without a Janus source identity",
    ]
    candidate_equations = [
        {
            "name": "E_phi_density",
            "formula": "delta_phi(B rho_to)=B phi^*(xi^a nabla_a rho_to + rho_to nabla_a xi^a)",
            "meaning": "density/volume pullback variation; after integration by parts it becomes a force-divergence map equation only if the action measure and boundary are fixed",
            "algebra_closed": True,
            "source_closed": False,
        },
        {
            "name": "E_phi_stress",
            "formula": "delta_phi(T_to->self)=phi^*(Lie_xi T_to) plus connection/pushforward terms",
            "meaning": "tensor source transport gives the non-scalar part of E_phi; it cannot be replaced by Q_det or Q_cross scalars",
            "algebra_closed": True,
            "source_closed": False,
        },
        {
            "name": "E_L_lorentz",
            "formula": "Lambda=delta L L^{-1}; E_L[Lambda]=antisym_AB((L^T P)_AB)=0",
            "meaning": "Lorentz-only L variation gives a tetrad torque/antisymmetric stress condition, not a unique bridge for symmetric dust",
            "algebra_closed": True,
            "source_closed": False,
        },
        {
            "name": "E_L_strain",
            "formula": "symmetric/trace-free L selection needs a GL/strain action and a stability gate",
            "meaning": "if Janus needs trace-free relative metric selection, Lorentz variation alone is insufficient",
            "algebra_closed": False,
            "source_closed": False,
        },
        {
            "name": "mirror_equations",
            "formula": "E_phi^-=(phi^{-1})_* E_phi^+ and E_L^-=-Ad_{L^{-1}} E_L^+",
            "meaning": "plus/minus equations must be inverse images of the same variational law",
            "algebra_closed": True,
            "source_closed": False,
        },
    ]
    open_requirements = [
        "identify the exact Janus cross-source action/source slot being varied",
        "fix the B_4vol/J_phi measure convention in that slot",
        "derive boundary and gauge conditions that make the phi equation invertible",
        "prove Lorentz-only L is enough or introduce a sourced GL/strain law with stability proof",
        "prove the mirror inverse equations before using the result in prediction code",
    ]
    return {
        "description": "P0 variational-origin gate for candidate Janus E_phi/E_L map equations.",
        "status": "candidate-ephi-el-derived-algebraically-source-action-open",
        "derive_from": derive_from,
        "not_derive_from": not_derive_from,
        "candidate_equations": candidate_equations,
        "open_requirements": open_requirements,
        "xi_variation_variable_closed": True,
        "lambda_variation_variable_closed": True,
        "e_phi_candidate_written": True,
        "e_l_candidate_written": True,
        "pure_pullback_selects_phi_l": False,
        "lorentz_l_selects_unique_bridge": False,
        "source_coupled_action_required": True,
        "published_janus_e_phi_supplied": False,
        "published_janus_e_l_supplied": False,
        "dynamic_phi_l_selection_closed": False,
        "uses_observational_fit": False,
        "qdet_qcross_scalar_absorption_allowed": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "E_phi/E_L must be derived from a Janus cross-source action or source functional. "
            "The local variational shapes are now explicit, but they do not select phi/L until "
            "the published/source action fixes the measure, boundary, mirror law and L sector."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Janus Phi/L E_phi/E_L Variational Origin Gate",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Xi variation variable closed: {payload['xi_variation_variable_closed']}",
        f"Lambda variation variable closed: {payload['lambda_variation_variable_closed']}",
        f"E_phi candidate written: {payload['e_phi_candidate_written']}",
        f"E_L candidate written: {payload['e_l_candidate_written']}",
        f"Pure pullback selects phi/L: {payload['pure_pullback_selects_phi_l']}",
        f"Lorentz L selects unique bridge: {payload['lorentz_l_selects_unique_bridge']}",
        f"Source-coupled action required: {payload['source_coupled_action_required']}",
        f"Published Janus E_phi supplied: {payload['published_janus_e_phi_supplied']}",
        f"Published Janus E_L supplied: {payload['published_janus_e_l_supplied']}",
        f"Dynamic phi/L selection closed: {payload['dynamic_phi_l_selection_closed']}",
        f"Uses observational fit: {payload['uses_observational_fit']}",
        f"Qdet/Qcross scalar absorption allowed: {payload['qdet_qcross_scalar_absorption_allowed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Derive From",
        "",
    ]
    lines.extend(f"- {item}" for item in payload["derive_from"])
    lines.extend(["", "## Not Derive From", ""])
    lines.extend(f"- {item}" for item in payload["not_derive_from"])
    lines.extend(
        [
            "",
            "## Candidate Equations",
            "",
            "| name | formula | meaning | algebra closed | source closed |",
            "|---|---|---|---:|---:|",
        ]
    )
    for row in payload["candidate_equations"]:
        lines.append(
            f"| {row['name']} | `{row['formula']}` | {row['meaning']} | "
            f"{row['algebra_closed']} | {row['source_closed']} |"
        )
    lines.extend(["", "## Open Requirements", ""])
    lines.extend(f"- {item}" for item in payload["open_requirements"])
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
