from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_stueckelberg_sheetwise_kinetic_transport_gate.md")
JSON_PATH = Path("outputs/reports/p0_stueckelberg_sheetwise_kinetic_transport_gate.json")


def build_payload() -> dict:
    equations = [
        "D_t f + v^i D_i f + A^i_Janus D_{v^i} f = 0",
        "A^i_Janus=-(Gamma^i_ab p^a p^b)/p^0",
        "f(x,p)=sum_s w_s(x) delta(p-p_s(x))",
        "T^{mu nu}=sum_s rho_s u_s^mu u_s^nu",
        "Q_cross_total=sum_s P_opt[g_plus,g_minus,L_s]:(rho_s u_s u_s)",
    ]
    sheet_rules = [
        {
            "rule": "pre_caustic_limit",
            "requirement": "single sheet recovers the existing dust phi/L branch",
            "closed": True,
        },
        {
            "rule": "sheetwise_same_l",
            "requirement": "each sheet uses its own L_s consistently for K/Q_cross/Vlasov",
            "closed": True,
        },
        {
            "rule": "sheet_sum_conservation",
            "requirement": "sum_s rho_s dV_s is conserved through sheet transport",
            "closed": False,
        },
        {
            "rule": "sheet_creation",
            "requirement": "caustic/splitting rules are source-derived, not fitted",
            "closed": False,
        },
        {
            "rule": "phase_space_measure",
            "requirement": "dP/B4vol convention is closed for the kinetic measure",
            "closed": False,
        },
    ]
    forbidden = [
        "single global phi/L after multistreaming",
        "sheet-specific fitted Q_cross amplitudes",
        "setting Q_ijk=0 to close the moment hierarchy",
        "using diagnostic Vlasov solver as physical closure",
    ]
    return {
        "description": "Route B gate: sheetwise kinetic transport as no-axiom alternative to one global phi/L.",
        "status": "sheetwise-kinetic-route-open",
        "equations": equations,
        "sheet_rules": sheet_rules,
        "forbidden_shortcuts": forbidden,
        "uses_single_global_phi_l": False,
        "requires_sheetwise_phi_l_or_full_f": True,
        "pre_caustic_single_sheet_recovers_dust": True,
        "sheet_sum_conservation_proved": False,
        "sheet_creation_source_derived": False,
        "phase_space_measure_closed": False,
        "qcross_projection_derived": False,
        "uses_observational_fit": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "The kinetic route can avoid a single global phi/L by using sheetwise maps "
            "or the full distribution f. It remains open until sheet conservation, "
            "sheet creation, phase-space measure and optical projection are source-derived."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Stueckelberg Sheetwise Kinetic Transport Gate",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Uses single global phi/L: {payload['uses_single_global_phi_l']}",
        f"Requires sheetwise phi/L or full f: {payload['requires_sheetwise_phi_l_or_full_f']}",
        f"Pre-caustic single sheet recovers dust: {payload['pre_caustic_single_sheet_recovers_dust']}",
        f"Sheet sum conservation proved: {payload['sheet_sum_conservation_proved']}",
        f"Sheet creation source-derived: {payload['sheet_creation_source_derived']}",
        f"Phase-space measure closed: {payload['phase_space_measure_closed']}",
        f"Q_cross projection derived: {payload['qcross_projection_derived']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Equations",
        "",
    ]
    lines.extend(f"- `{item}`" for item in payload["equations"])
    lines.extend(["", "## Sheet Rules", "", "| rule | requirement | closed |", "|---|---|---:|"])
    for row in payload["sheet_rules"]:
        lines.append(f"| {row['rule']} | {row['requirement']} | {row['closed']} |")
    lines.extend(["", "## Forbidden Shortcuts", ""])
    lines.extend(f"- {item}" for item in payload["forbidden_shortcuts"])
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
