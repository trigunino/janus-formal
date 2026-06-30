from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_source_congruence_omega_gate.md")
JSON_PATH = Path("outputs/reports/p0_source_congruence_omega_gate.json")


def build_payload() -> dict:
    equations = [
        {
            "name": "Lorentz transport",
            "form": "Omega_alpha=(D_alpha L)L^{-1}, Omega_{alpha AB}=-Omega_{alpha BA}",
            "status": "fixed-convention",
        },
        {
            "name": "Flow contraction",
            "form": "Omega_u=u^alpha Omega_alpha",
            "status": "fixed-convention",
        },
        {
            "name": "Geodesic source congruence",
            "form": "u^beta D_beta u^alpha=0",
            "status": "route-a-open",
        },
        {
            "name": "Cross-force replacement",
            "form": "u^beta D_beta u^alpha=f_cross^alpha, u_alpha f_cross^alpha=0",
            "status": "route-b-open",
        },
        {
            "name": "Transported tetrad relation",
            "form": "D_u e_A=Omega_u{}^B{}_A e_B, e_0=u",
            "status": "source-law-needed",
        },
        {
            "name": "Omega_u u target",
            "form": "Omega_u{}^A{}_B u^B=0, or source-force terms cancel the Omega_u u residual",
            "status": "unproved",
        },
        {
            "name": "Shared K/Q_cross closure",
            "form": "same L/Omega enters K transport and Q_cross optical contractions",
            "status": "unproved",
        },
    ]
    blockers = [
        "derive u.D u=0 from the source equations or derive a covariant f_cross replacement",
        "prove the transported tetrad relation fixes Omega_u u without gauge choice",
        "show the same L/Omega closes the K route and Q_cross route",
        "exclude post-hoc fitting of Omega components to the lensing residual",
        "bound caustics, non-dust stress, and noncomoving momentum terms outside this P0 artifact",
    ]
    routes = [
        {
            "route": "geodesic",
            "claim": "source congruence gives u.D u=0, transported e_0=u gives Omega_u u=0",
            "closed": False,
        },
        {
            "route": "cross_force",
            "claim": "replace geodesic law by f_cross and prove force terms cancel the Omega_u u source residual",
            "closed": False,
        },
    ]
    return {
        "description": "Bounded P0 gate for source congruence/geodesic or cross-force route to Omega_u u=0.",
        "status": "source-congruence-omega-gate-open",
        "scope": "rank-one dust/source-congruence algebra only",
        "geodesic_route_allowed": True,
        "cross_force_route_allowed": True,
        "transported_tetrad_required": True,
        "same_l_omega_required": True,
        "k_qcross_required": True,
        "fit_choice_allowed": False,
        "no_fit": True,
        "source_derivation_closed": False,
        "k_qcross_closed": False,
        "physics_closed": False,
        "prediction_ready": False,
        "prediction_claim": False,
        "equations": equations,
        "routes": routes,
        "blockers": blockers,
        "verdict": (
            "This artifact only lists the source-congruence routes to Omega_u u=0. "
            "Either u.D u=0 or a covariant cross-force replacement must be source-derived, "
            "then tied to the transported tetrad and the same L/Omega used for K and Q_cross. "
            "No fit is allowed, so the prediction claim remains false."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Source Congruence Omega Gate",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Scope: {payload['scope']}",
        f"Geodesic route allowed: {payload['geodesic_route_allowed']}",
        f"Cross-force route allowed: {payload['cross_force_route_allowed']}",
        f"Transported tetrad required: {payload['transported_tetrad_required']}",
        f"Same L/Omega required: {payload['same_l_omega_required']}",
        f"K/Q_cross required: {payload['k_qcross_required']}",
        f"Fit choice allowed: {payload['fit_choice_allowed']}",
        f"No fit: {payload['no_fit']}",
        f"Source derivation closed: {payload['source_derivation_closed']}",
        f"K/Q_cross closed: {payload['k_qcross_closed']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        f"Prediction claim: {payload['prediction_claim']}",
        "",
        "## Equations",
        "",
        "| name | form | status |",
        "|---|---|---|",
    ]
    for row in payload["equations"]:
        lines.append(f"| {row['name']} | `{row['form']}` | {row['status']} |")
    lines.extend(["", "## Routes", "", "| route | claim | closed |", "|---|---|---|"])
    for row in payload["routes"]:
        lines.append(f"| {row['route']} | {row['claim']} | {row['closed']} |")
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
