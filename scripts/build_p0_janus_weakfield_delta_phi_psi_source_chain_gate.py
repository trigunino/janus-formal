from __future__ import annotations

from pathlib import Path
import json
import sys


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_janus_weakfield_phi_psi_qdet_source_closure_attempt import (
    build_payload as build_phi_psi_qdet_attempt,
)
from scripts.build_p0_janus_weakfield_source_potential_system import (
    build_payload as build_source_potential_system,
)
from scripts.build_p0_janus_weakfield_delta_s00_source_expansion_gate import (
    build_payload as build_delta_s00_expansion,
)
from scripts.build_p0_janus_weakfield_delta_s00_measure_convention_gate import (
    build_payload as build_delta_s00_measure_convention,
)
from scripts.build_p0_janus_weakfield_delta_s00_density_transport_gate import (
    build_payload as build_delta_s00_density_transport,
)


REPORT_PATH = Path("outputs/reports/p0_janus_weakfield_delta_phi_psi_source_chain_gate.md")
JSON_PATH = Path("outputs/reports/p0_janus_weakfield_delta_phi_psi_source_chain_gate.json")


def build_payload() -> dict:
    source_potential = build_source_potential_system()
    qdet_attempt = build_phi_psi_qdet_attempt()
    delta_s00 = build_delta_s00_expansion()
    measure_convention = build_delta_s00_measure_convention()
    density_transport = build_delta_s00_density_transport()
    chain_rows = [
        {
            "name": "delta_psi_poisson",
            "equation": "2 Lap(Delta_Psi)=chi(delta_S00_minus-delta_S00_plus)",
            "source": "subtract weak-field plus/minus Poisson rows",
            "closed": True,
        },
        {
            "name": "plus_slip",
            "equation": "D_iD_j(Phi_plus-Psi_plus)=chi Pi_plus_effective_ij",
            "source": "plus trace-free spatial field equation",
            "closed": False,
        },
        {
            "name": "minus_slip",
            "equation": "D_iD_j(Phi_minus-Psi_minus)=-chi Pi_minus_effective_ij",
            "source": "minus trace-free spatial field equation",
            "closed": False,
        },
        {
            "name": "delta_phi_from_delta_psi_and_slip",
            "equation": "Delta_Phi=Delta_Psi+(Phi_minus-Psi_minus)-(Phi_plus-Psi_plus)",
            "source": "definition after slip rows",
            "closed": True,
        },
    ]
    open_requirements = [
        "solve delta_S00_plus/minus from Janus source slots including B4vol feedback",
        "derive Pi_plus_effective_ij and Pi_minus_effective_ij or prove dust Pi=0",
        "fix boundary/gauge zero modes before inverting Laplacians",
        "keep Q_det as density convention only, not curvature/lensing amplitude",
        "feed Delta_Phi/Delta_Psi into weak-field curvature rows only as restricted branch",
    ]
    return {
        "description": "Weak-field Janus source chain from cross-source rows to Delta_Psi and Delta_Phi.",
        "status": "delta-phi-psi-source-chain-written-physics-open",
        "depends_on": [
            "p0_janus_weakfield_source_potential_system",
            "p0_janus_weakfield_phi_psi_qdet_source_closure_attempt",
            "p0_janus_weakfield_delta_s00_source_expansion_gate",
            "p0_janus_weakfield_delta_s00_measure_convention_gate",
            "p0_janus_weakfield_delta_s00_density_transport_gate",
            "p0_weakfield_relative_curvature_rows_target",
        ],
        "feeds": [
            "p0_weakfield_curvature_injection_probe",
            "p0_weakfield_relative_curvature_rows_target",
        ],
        "source_potential_rows_written": bool(source_potential["poisson_rows_written"]),
        "slip_rows_written": bool(source_potential["slip_rows_written"]),
        "b4vol_feedback_written": bool(qdet_attempt["linearized_b4vol_feedback_written"]),
        "delta_s00_expansion_artifact": "p0_janus_weakfield_delta_s00_source_expansion_gate",
        "delta_s00_expansion_closed": bool(delta_s00["delta_s00_expansion_closed"]),
        "delta_s00_physics_closed": bool(delta_s00["physics_closed"]),
        "delta_s00_measure_convention_artifact": "p0_janus_weakfield_delta_s00_measure_convention_gate",
        "delta_s00_measure_convention_algebra_closed": bool(
            measure_convention["measure_convention_algebra_closed"]
        ),
        "delta_s00_field_residual_convention_selected": bool(
            measure_convention["field_residual_convention_selected"]
        ),
        "delta_s00_selected_field_residual_convention": measure_convention[
            "selected_field_residual_convention"
        ],
        "delta_s00_source_convention_selected": bool(
            measure_convention["source_convention_selected"]
        ),
        "delta_s00_density_transport_artifact": "p0_janus_weakfield_delta_s00_density_transport_gate",
        "delta_s00_density_transport_slot_written": bool(
            density_transport["weakfield_density_transport_slot_written"]
        ),
        "delta_s00_full_density_transport_closed": bool(
            density_transport["full_density_transport_closed"]
        ),
        "chain_rows": chain_rows,
        "delta_psi_poisson_row_derived": True,
        "delta_phi_definition_closed": True,
        "delta_phi_requires_slip": True,
        "dust_delta_phi_equals_delta_psi_conditional": True,
        "general_slip_source_closed": False,
        "source_potential_solution_closed": False,
        "boundary_gauge_closed": False,
        "qdet_absorption_allowed": False,
        "uses_observational_fit": False,
        "physics_closed": False,
        "prediction_ready": False,
        "open_requirements": open_requirements,
        "verdict": (
            "The source-to-potential chain is written: subtracting Janus weak-field "
            "Poisson rows gives Delta_Psi, and Delta_Phi follows only after slip rows. "
            "Dust may set Delta_Phi=Delta_Psi conditionally, but the general branch "
            "needs Pi/source and boundary/gauge closure."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Janus Weak-Field Delta Phi/Psi Source Chain Gate",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Source potential rows written: {payload['source_potential_rows_written']}",
        f"Slip rows written: {payload['slip_rows_written']}",
        f"B4vol feedback written: {payload['b4vol_feedback_written']}",
        f"Delta S00 expansion artifact: `{payload['delta_s00_expansion_artifact']}`",
        f"Delta S00 expansion closed: {payload['delta_s00_expansion_closed']}",
        f"Delta S00 physics closed: {payload['delta_s00_physics_closed']}",
        f"Delta S00 measure convention artifact: `{payload['delta_s00_measure_convention_artifact']}`",
        f"Delta S00 measure convention algebra closed: {payload['delta_s00_measure_convention_algebra_closed']}",
        f"Delta S00 field residual convention selected: {payload['delta_s00_field_residual_convention_selected']}",
        f"Delta S00 selected field residual convention: `{payload['delta_s00_selected_field_residual_convention']}`",
        f"Delta S00 source convention selected: {payload['delta_s00_source_convention_selected']}",
        f"Delta S00 density transport artifact: `{payload['delta_s00_density_transport_artifact']}`",
        f"Delta S00 density transport slot written: {payload['delta_s00_density_transport_slot_written']}",
        f"Delta S00 full density transport closed: {payload['delta_s00_full_density_transport_closed']}",
        f"Delta Psi Poisson row derived: {payload['delta_psi_poisson_row_derived']}",
        f"Delta Phi definition closed: {payload['delta_phi_definition_closed']}",
        f"Delta Phi requires slip: {payload['delta_phi_requires_slip']}",
        f"Dust Delta Phi equals Delta Psi conditional: {payload['dust_delta_phi_equals_delta_psi_conditional']}",
        f"General slip source closed: {payload['general_slip_source_closed']}",
        f"Qdet absorption allowed: {payload['qdet_absorption_allowed']}",
        f"Uses observational fit: {payload['uses_observational_fit']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Chain Rows",
        "",
        "| name | equation | source | closed |",
        "|---|---|---|---:|",
    ]
    for row in payload["chain_rows"]:
        lines.append(f"| {row['name']} | `{row['equation']}` | {row['source']} | {row['closed']} |")
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
