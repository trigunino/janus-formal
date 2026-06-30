from __future__ import annotations

from pathlib import Path
import json

import sympy as sp


REPORT_PATH = Path("outputs/reports/p0_janus_kinetic_moment_eos_pi_closure_target.md")
JSON_PATH = Path("outputs/reports/p0_janus_kinetic_moment_eos_pi_closure_target.json")


def decompose_second_moment() -> dict[str, sp.Expr]:
    pxx, pyy, pzz, pxy, pxz, pyz = sp.symbols("P_xx P_yy P_zz P_xy P_xz P_yz")
    pressure = sp.simplify((pxx + pyy + pzz) / 3)
    return {
        "p": pressure,
        "Pi_xx": sp.simplify(pxx - pressure),
        "Pi_yy": sp.simplify(pyy - pressure),
        "Pi_zz": sp.simplify(pzz - pressure),
        "Pi_xy": pxy,
        "Pi_xz": pxz,
        "Pi_yz": pyz,
        "trace_Pi": sp.simplify((pxx - pressure) + (pyy - pressure) + (pzz - pressure)),
    }


def build_payload() -> dict:
    decomposition = decompose_second_moment()
    moment_definitions = [
        {
            "moment": "density",
            "formula": "rho=m int f d^3v",
            "role": "zeroth moment",
        },
        {
            "moment": "momentum",
            "formula": "rho beta_i=m int v_i f d^3v",
            "role": "first moment / T0i dust limit",
        },
        {
            "moment": "stress",
            "formula": "P_ij=m int (v_i-beta_i)(v_j-beta_j) f d^3v",
            "role": "second central moment",
        },
        {
            "moment": "pressure",
            "formula": "p=Tr(P_ij)/3",
            "role": "isotropic second moment",
        },
        {
            "moment": "anisotropic_stress",
            "formula": "Pi_ij=P_ij-p delta_ij",
            "role": "trace-free second moment",
        },
    ]
    hierarchy_blockers = [
        "second-moment evolution depends on third moment / heat-flux tensor",
        "collisionless Vlasov route needs phase-space transport from Janus geodesics",
        "fluid closure route needs source-derived EOS or moment closure",
        "Pi=0 requires isotropic distribution preserved by transport, not just initial isotropy",
    ]
    closure_routes = [
        {
            "route": "cold_dust",
            "condition": "P_ij=0",
            "result": "p=0 and Pi_ij=0",
            "closed": "conditional",
        },
        {
            "route": "isotropic_velocity_dispersion",
            "condition": "P_ij=p delta_ij and preserved isotropy",
            "result": "Pi_ij=0 but EOS p(rho) still needed",
            "closed": False,
        },
        {
            "route": "full_kinetic",
            "condition": "derive f evolution and close or solve moment hierarchy",
            "result": "p and Pi source-derived",
            "closed": False,
        },
    ]
    return {
        "description": "Kinetic moment target for deriving Janus EOS and Pi from a distribution function.",
        "status": "kinetic-moment-eos-pi-closure-open",
        "depends_on": [
            "p0_janus_eos_pi_source_audit",
            "p0_stueckelberg_kinetic_transport_candidate",
            "p0_janus_pressure_pi0i_transport_derivation",
        ],
        "moment_definitions": moment_definitions,
        "second_moment_decomposition": {key: sp.sstr(value) for key, value in decomposition.items()},
        "hierarchy_blockers": hierarchy_blockers,
        "closure_routes": closure_routes,
        "second_moment_decomposition_derived": True,
        "trace_free_pi_verified": True,
        "dust_limit_recovers_p_zero_pi_zero": True,
        "eos_from_kinetic_moments_closed": False,
        "pi_evolution_from_kinetic_moments_closed": False,
        "hierarchy_closed": False,
        "uses_observational_fit": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "Kinetic moments provide the right non-rustine route for EOS and Pi. "
            "The algebraic decomposition is closed, but the hierarchy or distribution evolution "
            "must still be derived before general matter closure."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Janus Kinetic Moment EOS/Pi Closure Target",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Second moment decomposition derived: {payload['second_moment_decomposition_derived']}",
        f"Trace-free Pi verified: {payload['trace_free_pi_verified']}",
        f"Dust limit recovers p=0/Pi=0: {payload['dust_limit_recovers_p_zero_pi_zero']}",
        f"EOS from kinetic moments closed: {payload['eos_from_kinetic_moments_closed']}",
        f"Pi evolution from kinetic moments closed: {payload['pi_evolution_from_kinetic_moments_closed']}",
        f"Hierarchy closed: {payload['hierarchy_closed']}",
        f"Uses observational fit: {payload['uses_observational_fit']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Moment Definitions",
        "",
        "| moment | formula | role |",
        "|---|---|---|",
    ]
    for row in payload["moment_definitions"]:
        lines.append(f"| {row['moment']} | `{row['formula']}` | {row['role']} |")
    lines.extend(["", "## Second-Moment Decomposition", ""])
    lines.extend(f"- `{key}`: `{value}`" for key, value in payload["second_moment_decomposition"].items())
    lines.extend(["", "## Hierarchy Blockers", ""])
    lines.extend(f"- {item}" for item in payload["hierarchy_blockers"])
    lines.extend(["", "## Closure Routes", "", "| route | condition | result | closed |", "|---|---|---|---|"])
    for row in payload["closure_routes"]:
        lines.append(f"| {row['route']} | {row['condition']} | {row['result']} | {row['closed']} |")
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
