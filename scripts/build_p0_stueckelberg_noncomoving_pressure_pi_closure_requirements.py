from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_stueckelberg_noncomoving_pressure_pi_closure_requirements.md")
JSON_PATH = Path("outputs/reports/p0_stueckelberg_noncomoving_pressure_pi_closure_requirements.json")


def build_payload() -> dict:
    required_tensor_terms = [
        "perfect-fluid pressure metric term p g^{mu nu}",
        "projector h^{mu nu}=g^{mu nu}+u^mu u^nu",
        "anisotropic stress Pi^{mu nu}",
        "boosted Pi00 and momentum flux T0i",
        "cross-sector equation of state or proof p_cross=0",
        "divergence terms in R_plus/R_minus after pressure and Pi substitution",
    ]
    forbidden_shortcuts = [
        "do not absorb pressure into scalar Q_det",
        "do not absorb Pi^{mu nu} into scalar Q_cross",
        "do not claim dust closure proves perfect-fluid closure",
        "do not set Pi00=0 without a transported eigenframe or source proof",
    ]
    closure_gates = {
        "beta_source_derived": False,
        "pressure_eos_cross_derived": False,
        "pi_transport_or_zero_proof_available": False,
        "t0i_momentum_closure_available": False,
        "r_plus_pressure_pi_residual_closed": False,
        "r_minus_pressure_pi_residual_closed": False,
    }
    return {
        "description": "P0 closure requirements for extending non-comoving dust to pressure and anisotropic stress.",
        "status": "requirements-open",
        "required_tensor_terms": required_tensor_terms,
        "forbidden_shortcuts": forbidden_shortcuts,
        "closure_gates": closure_gates,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "Dust closure assumptions are insufficient for pressure or Pi. The extension "
            "requires tensor transport and residual cancellation, not scalar absorption."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Non-comoving Pressure/Pi Closure Requirements",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Required Tensor Terms",
        "",
    ]
    lines.extend(f"- {item}" for item in payload["required_tensor_terms"])
    lines.extend(["", "## Forbidden Shortcuts", ""])
    lines.extend(f"- {item}" for item in payload["forbidden_shortcuts"])
    lines.extend(["", "## Closure Gates", ""])
    lines.extend(f"- {key}: {value}" for key, value in payload["closure_gates"].items())
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
