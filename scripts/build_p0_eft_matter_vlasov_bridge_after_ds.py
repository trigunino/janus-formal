from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_eft_matter_vlasov_bridge_after_ds.md")
JSON_PATH = Path("outputs/reports/p0_eft_matter_vlasov_bridge_after_ds.json")


def build_payload() -> dict:
    inputs = {
        "ds_stability": "conditionally ready",
        "boundary_sector": "conditional APS/projector/eta closure",
        "metric_branch": "dS branch with boundary response bookkeeping",
    }
    matter_bridge = {
        "required_distribution": "f_plus(x,p), f_minus(x,p) on the two Janus sheets",
        "transport_operator": "same-bridge pullback of phase-space measure and geodesic flow",
        "stress_tensor": "T_self + transported T_other_to_self",
        "closure_target": "derive rho, pressure, Pi, and lensing source from moments of f",
    }
    theorem_status = {
        "ds_boundary_inputs_available": True,
        "matter_bridge_defined": True,
        "vlasov_equation_derived": False,
        "phase_space_measure_closed": False,
        "pressure_pi_moments_closed": False,
        "lensing_source_closed": False,
        "growth_observables_ready": False,
        "prediction_ready_unconditional": False,
    }
    obligations = [
        "derive the effective Vlasov equation on each sheet using the selected bridge",
        "derive the phase-space measure transport including B4vol/solder factors",
        "compute stress-tensor moments rho, p, Pi from f",
        "derive lensing/growth source terms from the transported stress tensor",
    ]
    return {
        "description": "Matter/Vlasov bridge after conditional dS stability closure.",
        "status": "matter-vlasov-open",
        "inputs": inputs,
        "matter_bridge": matter_bridge,
        "theorem_status": theorem_status,
        "obligations": obligations,
        "verdict": (
            "dS stability can now feed the matter pipeline conditionally. The next hard closure "
            "is Vlasov/phase-space transport and moment hierarchy."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 EFT Matter Vlasov Bridge After dS",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        "",
        "## Inputs",
    ]
    lines.extend(f"- {key}: {value}" for key, value in payload["inputs"].items())
    lines.extend(["", "## Matter Bridge"])
    lines.extend(f"- {key}: {value}" for key, value in payload["matter_bridge"].items())
    lines.extend(["", "## Status"])
    lines.extend(f"- {key}: {value}" for key, value in payload["theorem_status"].items())
    lines.extend(["", "## Obligations"])
    lines.extend(f"- {item}" for item in payload["obligations"])
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
