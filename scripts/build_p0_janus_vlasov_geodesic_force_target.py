from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_janus_vlasov_geodesic_force_target.md")
JSON_PATH = Path("outputs/reports/p0_janus_vlasov_geodesic_force_target.json")


def build_payload() -> dict:
    covariant_targets = [
        "mass shell: g_AB p^A p^B=-m^2",
        "Liouville: p^mu partial_mu f - Gamma^i_{alpha beta} p^alpha p^beta partial_{p^i} f=0",
        "force term: A^i_Janus=-(Gamma^i_{alpha beta} p^alpha p^beta)/(p^0) after slicing",
        "moments: T^{AB}=int p^A p^B f dP on the same measure branch",
    ]
    janus_requirements = [
        "choose source-derived plus/minus metrics before computing Gamma",
        "transport minus-sector momenta through the accepted same-L map before plus-observer moments",
        "keep B_4vol and phase-space dP as measure factors, not optical amplitudes",
        "use X2025 Vlasov/Poisson only as kinetic anchor until tensor metric branch is derived",
    ]
    weakfield_reduction_targets = [
        "A_i=-D_i Phi plus shift/lapse/connection corrections",
        "G0i shift source fixes beta_i only in the conditional dust/transverse limit",
        "trace-free D_i A_j feeds the Pi preservation gate",
    ]
    return {
        "description": "P0 target deriving the Vlasov force term from Janus geodesics and connection data.",
        "status": "vlasov-geodesic-force-target-open",
        "depends_on": [
            "p0_janus_full_vlasov_moment_closure_contract",
            "p0_janus_weakfield_source_potential_system",
            "p0_janus_weakfield_g0i_shift_operator_derivation",
        ],
        "covariant_targets": covariant_targets,
        "janus_requirements": janus_requirements,
        "weakfield_reduction_targets": weakfield_reduction_targets,
        "geodesic_force_formula_written": True,
        "a_janus_no_longer_free_symbol": True,
        "source_metric_required": True,
        "same_l_required": True,
        "weakfield_reduction_written": True,
        "weakfield_metric_force_probe_available": True,
        "phase_space_transport_source_derived": False,
        "uses_observational_fit": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "A^i_Janus should be computed from the Janus connection/geodesic flow. "
            "This removes a free-force shortcut, but closure still waits on the source-selected "
            "metric/tetrad branch and same-L transport."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Janus Vlasov Geodesic Force Target",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Geodesic force formula written: {payload['geodesic_force_formula_written']}",
        f"A_Janus no longer free symbol: {payload['a_janus_no_longer_free_symbol']}",
        f"Source metric required: {payload['source_metric_required']}",
        f"Same L required: {payload['same_l_required']}",
        f"Weak-field reduction written: {payload['weakfield_reduction_written']}",
        f"Weak-field metric force probe available: {payload['weakfield_metric_force_probe_available']}",
        f"Phase-space transport source-derived: {payload['phase_space_transport_source_derived']}",
        f"Uses observational fit: {payload['uses_observational_fit']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Covariant Targets",
        "",
    ]
    lines.extend(f"- `{item}`" for item in payload["covariant_targets"])
    lines.extend(["", "## Janus Requirements", ""])
    lines.extend(f"- {item}" for item in payload["janus_requirements"])
    lines.extend(["", "## Weak-Field Reduction Targets", ""])
    lines.extend(f"- {item}" for item in payload["weakfield_reduction_targets"])
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
