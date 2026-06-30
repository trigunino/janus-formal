from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_route_c_geometric_exotic_completion_gate.md")
JSON_PATH = Path("outputs/reports/p0_route_c_geometric_exotic_completion_gate.json")


def build_payload() -> dict:
    candidates = [
        {
            "route": "BF_connection",
            "equations": "F_Omega=Phi_R[source], D_alpha L-Omega_alpha L=0",
            "no_axiom_strength": "high-if-Phi_R-source-derived",
            "risk": "Phi_R missing",
        },
        {
            "route": "holonomy",
            "equations": "Omega=L^{-1}DL, F_Omega=R_self-L R_other L^{-1}",
            "no_axiom_strength": "high-local-geometry",
            "risk": "path-rule freedom",
        },
        {
            "route": "nonmetricity_cartan",
            "equations": "N_alpha=D_alpha H, D_[alpha N_beta]=[D_alpha,D_beta]H",
            "no_axiom_strength": "medium",
            "risk": "trace-free source missing",
        },
        {
            "route": "optimal_transport",
            "equations": "phi_*mu_plus=mu_minus, delta_phi C=0",
            "no_axiom_strength": "low-unless-cost-source-derived",
            "risk": "new principle",
        },
        {
            "route": "nonlocal_kernel",
            "equations": "G_source^{-1}(phi-f)=0",
            "no_axiom_strength": "low-unless-kernel-source-derived",
            "risk": "hides selector in kernel",
        },
    ]
    return {
        "description": "Route C gate for geometric and exotic no-axiom completions.",
        "status": "geometric-exotic-routes-ranked-open",
        "candidates": candidates,
        "preferred_order": ["BF_connection", "holonomy", "nonmetricity_cartan", "optimal_transport", "nonlocal_kernel"],
        "requires_same_l_for_k_qcross_vlasov": True,
        "prediction_ready": False,
        "uses_observational_fit": False,
        "physics_closed": False,
        "verdict": (
            "BF/connection and holonomy are the strongest no-axiom geometric routes because "
            "they can be tied to curvature. OT and nonlocal kernels remain lower-ranked unless "
            "their cost/kernel is source-derived."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Route C Geometric Exotic Completion Gate",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Preferred order: `{payload['preferred_order']}`",
        f"Requires same L for K/Q_cross/Vlasov: {payload['requires_same_l_for_k_qcross_vlasov']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "| route | equations | no-axiom strength | risk |",
        "|---|---|---|---|",
    ]
    for row in payload["candidates"]:
        lines.append(f"| {row['route']} | `{row['equations']}` | {row['no_axiom_strength']} | {row['risk']} |")
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
