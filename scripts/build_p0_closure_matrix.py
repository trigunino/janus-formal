from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_closure_matrix.md")
JSON_PATH = Path("outputs/reports/p0_closure_matrix.json")


P0_TRACKS = [
    {
        "track": "Bianchi residual closure",
        "current_artifacts": [
            "bianchi_mixed_stress_residual_target",
            "bianchi_lorentz_residual_reduction",
            "bianchi_connection_force_cancellation_target",
            "bianchi_transport_continuity_force_target",
            "bianchi_conditional_closure_theorem",
        ],
        "proof_obligation": "prove R_plus^mu=0 and R_minus^mu=0 from source-derived transport",
        "status": "open",
    },
    {
        "track": "Cross transport maps L_plus_minus",
        "current_artifacts": [
            "qcross_tetrad_map_target",
            "qcross_geometric_tetrad_map_derivation",
            "bianchi_mixed_transport_map_target",
            "bianchi_l_map_source_equations_target",
            "p0_l_k_qcross_consistency_target",
        ],
        "proof_obligation": "derive L_minus_to_plus and L_plus_to_minus from Janus equations, not from lensing data",
        "status": "open",
    },
    {
        "track": "L-derivative terms",
        "current_artifacts": [
            "bianchi_l_derivative_obstruction",
            "bianchi_connection_force_cancellation_target",
            "bianchi_transported_geodesic_force_target",
            "bianchi_l_map_source_equations_target",
            "bianchi_transport_continuity_force_target",
        ],
        "proof_obligation": "derive D L terms or prove cancellation against connection-difference forces",
        "status": "open",
    },
    {
        "track": "Transported continuity",
        "current_artifacts": [
            "bianchi_lorentz_residual_reduction",
            "bianchi_connection_force_cancellation_target",
            "bianchi_transported_continuity_target",
            "bianchi_transport_continuity_force_target",
        ],
        "proof_obligation": "prove D_minus(rho_minus u_minus_to_plus)=0 and D_plus(rho_plus u_plus_to_minus)=0",
        "status": "open",
    },
    {
        "track": "Connection-force cancellation",
        "current_artifacts": [
            "bianchi_l_derivative_obstruction",
            "bianchi_connection_force_cancellation_target",
            "bianchi_transported_geodesic_force_target",
            "bianchi_transport_continuity_force_target",
        ],
        "proof_obligation": "prove transported acceleration plus/minus C force equations in both sectors",
        "status": "open",
    },
    {
        "track": "K_plus K_minus compatibility",
        "current_artifacts": [
            "bianchi_mixed_transport_map_target",
            "qcross_tetrad_map_target",
            "lensing_qdet_qcross_derivation_map",
            "bianchi_l_map_source_equations_target",
            "p0_l_k_qcross_consistency_target",
        ],
        "proof_obligation": "prove the same L maps induce optical Q_cross and Bianchi K_plus/K_minus",
        "status": "open",
    },
    {
        "track": "Matter extension dust perfect anisotropic",
        "current_artifacts": [
            "bianchi_lorentz_boost_transport_branch",
            "bianchi_flrw_perfect_fluid_transport_branch",
            "bianchi_anisotropic_stress_transport_target",
            "bianchi_tensor_matter_extension_target",
        ],
        "proof_obligation": "extend closure from dust to perfect fluid and anisotropic stress without scalar shortcuts",
        "status": "open",
    },
]


def build_payload() -> dict:
    return {
        "description": "Exhaustive P0 closure matrix for the current Janus proof/simulation blockers.",
        "all_p0_closed": False,
        "prediction_ready": False,
        "tracks": P0_TRACKS,
        "next_parallel_work": [
            "source-derive L_minus_to_plus/L_plus_to_minus",
            "prove transported continuity equations",
            "prove connection-force cancellation equations",
            "extend K transport from dust to perfect fluid and anisotropic stress",
        ],
        "verdict": (
            "Every P0 track has a named proof obligation. None is closed for final "
            "prediction until all tracks are source-derived and mutually compatible."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Closure Matrix",
        "",
        payload["description"],
        "",
        f"All P0 closed: {payload['all_p0_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "| track | artifacts | proof obligation | status |",
        "|---|---|---|---|",
    ]
    for row in payload["tracks"]:
        artifacts = ", ".join(row["current_artifacts"])
        lines.append(
            f"| {row['track']} | `{artifacts}` | {row['proof_obligation']} | {row['status']} |"
        )
    lines.extend(["", "## Next Parallel Work", ""])
    lines.extend(f"- {item}" for item in payload["next_parallel_work"])
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
