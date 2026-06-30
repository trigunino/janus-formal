from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_eft_cosmology_conditional_bridge.md")
JSON_PATH = Path("outputs/reports/p0_eft_cosmology_conditional_bridge.json")


def build_payload() -> dict:
    boundary_input = {
        "boundary_spectral_status": "prediction_ready_conditional",
        "run1": "boundary Euler-Lagrange projector closes conditionally",
        "run2": "APS/eta zero-mode sector closes conditionally",
        "effective_use": "allowed as a conditional boundary sector in the dS perturbation pipeline",
    }
    cosmology_bridge = {
        "tensor_sector": "can import boundary response conditions into dS tensor stability checks",
        "scalar_sector": "must keep boundary response beta and volume lambda as conditional assumptions",
        "vlasov_matter_sector": "not closed by this boundary result",
        "observables": "H0/JWST/growth/lensing remain downstream, not proved here",
    }
    theorem_status = {
        "boundary_sector_conditionally_ready": True,
        "can_feed_ds_perturbation_pipeline": True,
        "full_cosmology_prediction_ready": False,
        "matter_vlasov_closed": False,
        "observables_derived": False,
        "prediction_ready_unconditional": False,
    }
    obligations = [
        "import conditional boundary assumptions into the dS scalar/tensor perturbation reports",
        "verify no previous dS stability expression used incompatible boundary assumptions",
        "propagate beta response and volume lambda into the effective stress/source bookkeeping",
        "then resume matter/Vlasov/lensing/growth closure",
    ]
    return {
        "description": "Bridge from conditional boundary/spectral closure to the cosmology pipeline.",
        "status": "boundary-ready-cosmology-not-ready",
        "boundary_input": boundary_input,
        "cosmology_bridge": cosmology_bridge,
        "theorem_status": theorem_status,
        "obligations": obligations,
        "verdict": (
            "The boundary sector may now be used as a conditional input for dS perturbations. "
            "It does not close the full cosmology: matter/Vlasov and observable predictions remain open."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 EFT Cosmology Conditional Bridge",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        "",
        "## Boundary Input",
    ]
    lines.extend(f"- {key}: {value}" for key, value in payload["boundary_input"].items())
    lines.extend(["", "## Cosmology Bridge"])
    lines.extend(f"- {key}: {value}" for key, value in payload["cosmology_bridge"].items())
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
