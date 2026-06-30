from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_janus_phase_space_b4vol_measure_gate.md")
JSON_PATH = Path("outputs/reports/p0_janus_phase_space_b4vol_measure_gate.json")


def build_payload() -> dict:
    measure_factors = [
        "B_4vol: spacetime determinant/source density weight",
        "dP: invariant mass-shell momentum measure",
        "J_phi: pullback Jacobian for map/source labels",
        "Q_det: metric-volume density map, not optical amplitude",
        "Q_cross: optical/tetrad contraction, not density measure",
    ]
    closure_identities = [
        "D_receiver(B_4vol rho_to u_to)=0 for pulled dust branch",
        "T^{AB}=int p^A p^B f dP with the selected metric branch",
        "rho_to and f_to use the same source density convention",
        "no double-counting between B_4vol, J_phi, and Q_det",
    ]
    blockers = [
        "source-selected lapse/slice/determinant convention",
        "phase-space measure after cross-sector momentum map",
        "proof that B_4vol used by matter action matches field-equation source density",
        "compatibility with same-L kinetic moment projection",
    ]
    return {
        "description": "P0 gate for closing phase-space measure, B_4vol, J_phi, and Q_det conventions.",
        "status": "phase-space-b4vol-measure-gate-open",
        "depends_on": [
            "p0_stueckelberg_density_measure_identity_lock",
            "p0_density_measure_branch_decision_gate",
            "p0_janus_full_vlasov_moment_closure_contract",
        ],
        "measure_factors": measure_factors,
        "closure_identities": closure_identities,
        "blockers": blockers,
        "measure_factors_separated": True,
        "qdet_not_optical_amplitude": True,
        "qcross_not_density_measure": True,
        "phase_space_measure_probe_available": True,
        "weakfield_b4vol_product_rule_probe_available": True,
        "b4vol_phase_space_measure_closed": False,
        "uses_observational_fit": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "The measure problem is now explicit: B_4vol, dP, J_phi, Q_det, and Q_cross "
            "must remain separate until source/lapse/slice identities prove their product rules."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Janus Phase-Space B4vol Measure Gate",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Measure factors separated: {payload['measure_factors_separated']}",
        f"Q_det not optical amplitude: {payload['qdet_not_optical_amplitude']}",
        f"Q_cross not density measure: {payload['qcross_not_density_measure']}",
        f"Phase-space measure probe available: {payload['phase_space_measure_probe_available']}",
        "Weak-field B4vol product-rule probe available: "
        f"{payload['weakfield_b4vol_product_rule_probe_available']}",
        f"B4vol phase-space measure closed: {payload['b4vol_phase_space_measure_closed']}",
        f"Uses observational fit: {payload['uses_observational_fit']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Measure Factors",
        "",
    ]
    lines.extend(f"- {item}" for item in payload["measure_factors"])
    lines.extend(["", "## Closure Identities", ""])
    lines.extend(f"- `{item}`" for item in payload["closure_identities"])
    lines.extend(["", "## Blockers", ""])
    lines.extend(f"- {item}" for item in payload["blockers"])
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
