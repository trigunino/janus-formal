from __future__ import annotations

from pathlib import Path
import json

import sympy as sp


REPORT_PATH = Path("outputs/reports/p0_cold_vlasov_dust_preservation_probe.md")
JSON_PATH = Path("outputs/reports/p0_cold_vlasov_dust_preservation_probe.json")


def build_payload() -> dict:
    rho1, rho2, u1, u2 = sp.symbols("rho1 rho2 u1 u2", positive=True)
    rho = rho1 + rho2
    beta = sp.simplify((rho1 * u1 + rho2 * u2) / rho)
    pressure_1d = sp.factor(rho1 * (u1 - beta) ** 2 + rho2 * (u2 - beta) ** 2)
    pressure_expected = sp.factor(rho1 * rho2 * (u1 - u2) ** 2 / rho)
    pressure_matches = bool(sp.simplify(pressure_1d - pressure_expected) == 0)
    p_iso = sp.factor(pressure_1d / 3)
    pi_xx = sp.factor(pressure_1d - p_iso)
    pi_yy = sp.factor(-p_iso)
    single_stream_conditions = [
        "f_s(x,v,t)=rho_s(x,t) delta(v-u_s(x,t)) for each sector",
        "characteristic map x0 -> x(t,x0) remains invertible",
        "Janus force is single-valued on the chosen sector sheet",
        "same L/B4vol transport is already source-selected",
    ]
    failure_modes = [
        "shell crossing or multistreaming creates velocity dispersion",
        "force/tetrad map becomes multivalued",
        "different streams are projected with different L maps",
        "coarse graining a cold sheet creates effective pressure",
    ]
    return {
        "description": "Internal kinetic probe for whether a cold Vlasov branch preserves dust p=0 and Pi=0.",
        "status": "cold-vlasov-dust-preservation-conditional",
        "two_stream_beta": str(beta),
        "two_stream_pressure": str(pressure_1d),
        "two_stream_pressure_expected": str(pressure_expected),
        "pressure_formula_verified": pressure_matches,
        "two_stream_p_iso": str(p_iso),
        "two_stream_pi_diag": [str(pi_xx), str(pi_yy), str(pi_yy)],
        "single_stream_conditions": single_stream_conditions,
        "failure_modes": failure_modes,
        "single_stream_preserves_p_zero": True,
        "single_stream_preserves_pi_zero": True,
        "multistream_generates_pressure": True,
        "multistream_generates_pi": True,
        "dust_branch_closed_conditionally": True,
        "general_dust_closure_proved": False,
        "same_l_b4vol_still_required": True,
        "uses_observational_fit": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "Cold Vlasov gives a valid conditional dust branch only before shell crossing. "
            "A two-stream counterexample generates pressure and anisotropic stress, so p=0 "
            "and Pi=0 cannot be promoted to a general Janus closure."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Cold Vlasov Dust Preservation Probe",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Two-stream beta: `{payload['two_stream_beta']}`",
        f"Two-stream pressure: `{payload['two_stream_pressure']}`",
        f"Pressure formula verified: {payload['pressure_formula_verified']}",
        f"Two-stream Pi diag: `{payload['two_stream_pi_diag']}`",
        f"Single-stream preserves p=0: {payload['single_stream_preserves_p_zero']}",
        f"Single-stream preserves Pi=0: {payload['single_stream_preserves_pi_zero']}",
        f"Multistream generates pressure: {payload['multistream_generates_pressure']}",
        f"Multistream generates Pi: {payload['multistream_generates_pi']}",
        f"Dust branch closed conditionally: {payload['dust_branch_closed_conditionally']}",
        f"General dust closure proved: {payload['general_dust_closure_proved']}",
        f"Same L/B4vol still required: {payload['same_l_b4vol_still_required']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Single-Stream Conditions",
        "",
    ]
    lines.extend(f"- {item}" for item in payload["single_stream_conditions"])
    lines.extend(["", "## Failure Modes", ""])
    lines.extend(f"- {item}" for item in payload["failure_modes"])
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
