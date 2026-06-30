from __future__ import annotations

from pathlib import Path
import json
import sys

import sympy as sp


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_cold_vlasov_dust_preservation_probe import (
    build_payload as build_cold_vlasov_probe,
)


REPORT_PATH = Path("outputs/reports/p0_scouple_matter_invariant_solver.md")
JSON_PATH = Path("outputs/reports/p0_scouple_matter_invariant_solver.json")


def build_payload() -> dict:
    cold_vlasov = build_cold_vlasov_probe()
    rho, p, pi, a, b, c = sp.symbols("rho p Pi a b c")
    i_matter = a * rho + b * p + c * pi
    dust_limit = sp.simplify(i_matter.subs({p: 0, pi: 0}))
    dust_match = sp.solve([dust_limit - rho], [a], dict=True)
    perfect_fluid_free = sp.simplify(i_matter.subs({pi: 0, a: 1}) - rho)
    anisotropic_free = sp.simplify(i_matter.subs({a: 1}) - rho)
    scalar_absorption_solutions = {
        "dust": str(dust_match),
        "perfect_fluid_without_eos": str(sp.solve([perfect_fluid_free], [b], dict=True)),
        "anisotropic_without_pi_law": str(sp.solve([anisotropic_free], [b, c], dict=True)),
    }
    tensor_terms = [
        {
            "term": "rho",
            "coefficient": "a",
            "dust_fixed": True,
            "requires_tensor_law": False,
        },
        {
            "term": "p",
            "coefficient": "b",
            "dust_fixed": False,
            "requires_tensor_law": True,
        },
        {
            "term": "Pi",
            "coefficient": "c",
            "dust_fixed": False,
            "requires_tensor_law": True,
        },
    ]
    closure_checks = [
        {
            "check": "dust_limit",
            "result": "a=1 fixes the dust contraction",
            "closed": True,
        },
        {
            "check": "perfect_fluid",
            "result": "b is not fixed without EOS/pressure transport",
            "closed": False,
        },
        {
            "check": "anisotropic_stress",
            "result": "c is not fixed without Pi tensor orientation and transport",
            "closed": False,
        },
        {
            "check": "scalar_absorption",
            "result": "setting b=c=0 recovers dust but discards pressure/Pi instead of deriving them",
            "closed": False,
        },
    ]
    return {
        "description": "Internal symbolic solver for matter invariants inside a candidate S_couple.",
        "status": "matter-invariant-family-open",
        "candidate_invariant": "I_matter=a*rho+b*p+c*Pi",
        "i_matter": str(i_matter),
        "dust_limit": str(dust_limit),
        "scalar_absorption_solutions": scalar_absorption_solutions,
        "tensor_terms": tensor_terms,
        "closure_checks": closure_checks,
        "cold_vlasov_probe_status": cold_vlasov["status"],
        "dust_branch_closed_conditionally": cold_vlasov["dust_branch_closed_conditionally"],
        "general_dust_closure_proved": cold_vlasov["general_dust_closure_proved"],
        "multistream_generates_pressure": cold_vlasov["multistream_generates_pressure"],
        "multistream_generates_pi": cold_vlasov["multistream_generates_pi"],
        "dust_coefficient_fixed": True,
        "pressure_coefficient_source_fixed": False,
        "pi_coefficient_source_fixed": False,
        "eos_required": True,
        "pi_transport_required": True,
        "scalar_q_absorption_allowed": False,
        "matter_family_unique": False,
        "uses_observational_fit": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "The internal matter-invariant attempt fixes only the dust coefficient. "
            "Pressure and Pi introduce independent tensor data; scalar absorption would "
            "delete, not derive, those terms."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 S_couple Matter Invariant Solver",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Candidate invariant: `{payload['candidate_invariant']}`",
        f"Cold Vlasov probe status: {payload['cold_vlasov_probe_status']}",
        f"Dust branch closed conditionally: {payload['dust_branch_closed_conditionally']}",
        f"General dust closure proved: {payload['general_dust_closure_proved']}",
        f"Multistream generates pressure: {payload['multistream_generates_pressure']}",
        f"Multistream generates Pi: {payload['multistream_generates_pi']}",
        f"Dust coefficient fixed: {payload['dust_coefficient_fixed']}",
        f"Pressure coefficient source fixed: {payload['pressure_coefficient_source_fixed']}",
        f"Pi coefficient source fixed: {payload['pi_coefficient_source_fixed']}",
        f"EOS required: {payload['eos_required']}",
        f"Pi transport required: {payload['pi_transport_required']}",
        f"Scalar Q absorption allowed: {payload['scalar_q_absorption_allowed']}",
        f"Matter family unique: {payload['matter_family_unique']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Scalar Absorption Solutions",
        "",
    ]
    for name, value in payload["scalar_absorption_solutions"].items():
        lines.append(f"- {name}: `{value}`")
    lines.extend(["", "## Tensor Terms", "", "| term | coefficient | dust fixed | requires tensor law |", "|---|---|---:|---:|"])
    for row in payload["tensor_terms"]:
        lines.append(
            f"| {row['term']} | `{row['coefficient']}` | {row['dust_fixed']} | {row['requires_tensor_law']} |"
        )
    lines.extend(["", "## Closure Checks", "", "| check | result | closed |", "|---|---|---:|"])
    for row in payload["closure_checks"]:
        lines.append(f"| {row['check']} | {row['result']} | {row['closed']} |")
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
