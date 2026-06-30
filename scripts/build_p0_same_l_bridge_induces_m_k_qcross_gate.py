from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_same_l_bridge_induces_m_k_qcross_gate.md")
JSON_PATH = Path("outputs/reports/p0_same_l_bridge_induces_m_k_qcross_gate.json")


def build_payload() -> dict:
    bridge_definitions = [
        {
            "name": "single_tetrad_bridge",
            "formula": "L_{o->s}^{A}{}_{B} maps other-sector tetrad components into self-sector tetrad components",
            "meaning": "one admissible tetrad bridge is the only transport datum",
        },
        {
            "name": "coordinate_bridge",
            "formula": "M_{o->s}^{mu}{}_{alpha}=e_s^{mu}{}_{A} L_{o->s}^{A}{}_{B} e_o^{B}{}_{alpha}",
            "meaning": "the coordinate-index bridge is induced by tetrads and the same L",
        },
        {
            "name": "stress_transport",
            "formula": "K_s^{mu nu}=T_{o->s}^{mu nu}=M_{o->s}^{mu}{}_{alpha} M_{o->s}^{nu}{}_{beta} T_o^{alpha beta}",
            "meaning": "K is not independent once M is induced by L",
        },
        {
            "name": "optical_qcross",
            "formula": "Q_cross,s=(eta_AB u_{o->s}^{A} k_s^{B})^2/(eta_AB u_s^{A} k_s^{B})^2; u_{o->s}^{A}=L_{o->s}^{A}{}_{B}u_o^{B}",
            "meaning": "Q_cross uses the same L as K, but is only an optical contraction factor",
        },
        {
            "name": "vlasov_moment_transport",
            "formula": "p_{o->s}^{A}=L_{o->s}^{A}{}_{B}p_o^{B}; moments use the same pushforward and phase-space measure",
            "meaning": "kinetic quadrupoles cannot choose a separate bridge",
        },
        {
            "name": "mirror_branch",
            "formula": "L_{s->o}=L_{o->s}^{-1} or a source-derived mirror with identical inverse action",
            "meaning": "plus/minus closure requires the mirror bridge, not an independent fit",
        },
    ]
    algebraic_results = [
        {
            "claim": "same_l_induces_m",
            "result": "M is fixed by e_s, e_o and L; no separate coordinate bridge is available",
            "closed": True,
        },
        {
            "claim": "same_l_induces_k",
            "result": "K_s is the rank-2 pushforward of T_o through M(L)",
            "closed": True,
        },
        {
            "claim": "same_l_induces_qcross",
            "result": "Q_cross is the null-observer contraction of the same tetrad bridge L",
            "closed": True,
        },
        {
            "claim": "same_l_induces_vlasov_moments",
            "result": "phase-space moment transport uses the same momentum pushforward p -> Lp",
            "closed": True,
        },
        {
            "claim": "no_scalar_absorption",
            "result": "B4vol/Q_det are scalar measure factors and Q_cross is optical; neither can absorb tensor-bridge residuals",
            "closed": True,
        },
    ]
    open_requirements = [
        "derive or source-select L_{o->s} from Janus equations/action/symmetry",
        "prove Lorentz/tetrad admissibility L^T eta L=eta on the selected branch",
        "prove the mirror inverse L_{s->o}=L_{o->s}^{-1} or derive the same result from Janus",
        "use the spin-connection identity D L=partial L+omega_s L-L omega_o, then source-select L/Omega",
        "close R_plus=0 and R_minus=0 with the same L, M, K, Q_cross and kinetic moments",
    ]
    return {
        "description": "Bounded P0 gate showing one admissible L algebraically induces M, K, Q_cross and Vlasov moment transport.",
        "status": "same-l-bridge-stack-algebra-closed-source-open",
        "depends_on": ["p0_same_l_spin_connection_transport_identity_gate"],
        "bridge_definitions": bridge_definitions,
        "algebraic_results": algebraic_results,
        "same_l_induces_m": True,
        "same_l_induces_k": True,
        "same_l_induces_qcross": True,
        "same_l_induces_vlasov_moments": True,
        "same_l_stack_algebra_closed": True,
        "scalar_absorption_allowed": False,
        "qcross_is_measure": False,
        "b4vol_is_stf_source": False,
        "l_source_selected": False,
        "lorentz_admissibility_proved": False,
        "mirror_inverse_proved": False,
        "dl_source_derived": False,
        "curvature_integrability_closed": False,
        "bianchi_residuals_closed": False,
        "physics_closed": False,
        "prediction": False,
        "prediction_ready": False,
        "open_requirements": open_requirements,
        "verdict": (
            "A single admissible tetrad bridge L is enough to fix M, K, Q_cross "
            "and kinetic moment transport algebraically. This removes separate "
            "bridge freedom, but it is not a prediction until Janus source-selects "
            "L and closes the mirror, D L and Bianchi residuals."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Same-L Bridge Induces M/K/Q_cross Gate",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Same L induces M: {payload['same_l_induces_m']}",
        f"Same L induces K: {payload['same_l_induces_k']}",
        f"Same L induces Q_cross: {payload['same_l_induces_qcross']}",
        f"Same L induces Vlasov moments: {payload['same_l_induces_vlasov_moments']}",
        f"Same-L stack algebra closed: {payload['same_l_stack_algebra_closed']}",
        f"Scalar absorption allowed: {payload['scalar_absorption_allowed']}",
        f"L source selected: {payload['l_source_selected']}",
        f"Lorentz admissibility proved: {payload['lorentz_admissibility_proved']}",
        f"Bianchi residuals closed: {payload['bianchi_residuals_closed']}",
        f"Prediction: {payload['prediction']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Bridge Definitions",
        "",
        "| name | formula | meaning |",
        "|---|---|---|",
    ]
    for row in payload["bridge_definitions"]:
        lines.append(f"| {row['name']} | `{row['formula']}` | {row['meaning']} |")
    lines.extend(["", "## Algebraic Results", "", "| claim | result | closed |", "|---|---|---:|"])
    for row in payload["algebraic_results"]:
        lines.append(f"| {row['claim']} | {row['result']} | {row['closed']} |")
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
