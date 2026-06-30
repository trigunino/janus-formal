from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_omega_closure_routes_gate.md")
JSON_PATH = Path("outputs/reports/p0_omega_closure_routes_gate.json")


def build_payload() -> dict:
    routes = [
        {
            "route": "source_omega_u_zero",
            "condition": "derive Omega u=0 along the transported dust congruence",
            "closed": False,
        },
        {
            "route": "projection_annihilation",
            "condition": "prove a source-derived projection P kills P L(Omega^T T+T Omega)L^T P^T",
            "closed": False,
        },
        {
            "route": "mirror_inverse_omega",
            "condition": "prove plus/minus Omega data are inverse-compatible",
            "closed": False,
        },
        {
            "route": "same_l_omega_observables",
            "condition": "use the same L/Omega for K transport, Q_cross, and lensing projection",
            "closed": False,
        },
    ]
    return {
        "description": "Gate collecting admissible routes to close the Omega residual.",
        "status": "omega-closure-routes-open",
        "routes": routes,
        "source_omega_u_zero_route_available": True,
        "omega_u_zero_source_derivation_target_available": True,
        "projection_annihilation_route_available": True,
        "omega_projection_annihilation_gate_available": True,
        "mirror_inverse_route_required": True,
        "same_l_omega_observable_route_required": True,
        "no_fit_route_selection": True,
        "omega_residual_closed": False,
        "pulled_m_metric_response_closed": False,
        "prediction_ready": False,
        "physics_closed": False,
        "verdict": (
            "Omega can close only through a source-derived Omega u=0 condition or a "
            "source-derived projection annihilation, with mirror and K/Q_cross consistency."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Omega Closure Routes Gate",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Source Omega u=0 route available: {payload['source_omega_u_zero_route_available']}",
        f"Omega u=0 source derivation target available: {payload['omega_u_zero_source_derivation_target_available']}",
        f"Projection annihilation route available: {payload['projection_annihilation_route_available']}",
        f"Omega projection annihilation gate available: {payload['omega_projection_annihilation_gate_available']}",
        f"Mirror inverse route required: {payload['mirror_inverse_route_required']}",
        f"Same L/Omega observable route required: {payload['same_l_omega_observable_route_required']}",
        f"No-fit route selection: {payload['no_fit_route_selection']}",
        f"Omega residual closed: {payload['omega_residual_closed']}",
        f"Pulled M metric response closed: {payload['pulled_m_metric_response_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Routes",
        "",
    ]
    for row in payload["routes"]:
        lines.append(f"- {row['route']}: {row['condition']} (closed: {row['closed']})")
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
