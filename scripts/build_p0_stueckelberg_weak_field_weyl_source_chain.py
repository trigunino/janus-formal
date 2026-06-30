from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_stueckelberg_weak_field_weyl_source_chain.md")
JSON_PATH = Path("outputs/reports/p0_stueckelberg_weak_field_weyl_source_chain.json")


def build_payload() -> dict:
    chain = [
        "rho_eff_plus = rho_plus - rho_minus_eff from the declared Janus weak-field source convention",
        "Delta Phi_lens_plus = 4 pi G rho_eff_plus on a periodic diagnostic slice",
        "kappa = 1/2 screen_trace Hessian(Phi_lens_plus)",
        "gamma1,gamma2 = screen_trace_free Hessian(Phi_lens_plus)",
    ]
    guards = [
        "source_provenance must not be survey_fit, shear_fit, sigma8_fit or S8_fit",
        "Q_det and Q_cross remain source/projection factors, not shear residual absorbers",
        "prediction_ready stays false until Phi_lens_plus is derived from delta G_plus[h_plus]",
        "restricted_metric_closure=True may mark only the comoving scalar zero-Pi branch as metric-ready",
        "full tensor Weyl still requires receiver metric perturbation, gauge and ray bundle",
    ]
    decision = {
        "weak_field_source_to_weyl_chain_available": True,
        "fit_provenance_rejected": True,
        "restricted_metric_ready_flag_available": True,
        "metric_potential_source_derived_from_full_janus": False,
        "full_tensor_weyl_closed": False,
        "prediction_ready": False,
    }
    return {
        "artifact": "p0_stueckelberg_weak_field_weyl_source_chain",
        "status": "weak-field-source-chain-diagnostic",
        "fit_used": False,
        "free_parameters": [],
        "physics_closed": False,
        "prediction_ready": False,
        "code_surface": "janus_lab.lensing.positive_photon_weak_field_weyl_components_2d",
        "chain": chain,
        "guards": guards,
        "decision": decision,
    }


def render_markdown(payload: dict) -> str:
    decision = payload["decision"]
    lines = [
        "# P0 Stueckelberg Weak Field Weyl Source Chain",
        "",
        f"Status: {payload['status']}",
        f"Code surface: `{payload['code_surface']}`",
        f"Fit used: {payload['fit_used']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Chain",
    ]
    lines.extend(f"- {item}" for item in payload["chain"])
    lines.extend(["", "## Guards"])
    lines.extend(f"- {item}" for item in payload["guards"])
    lines.extend(
        [
            "",
            "## Decision",
            f"Weak-field source-to-Weyl chain available: {decision['weak_field_source_to_weyl_chain_available']}",
            f"Fit provenance rejected: {decision['fit_provenance_rejected']}",
            f"Restricted metric-ready flag available: {decision['restricted_metric_ready_flag_available']}",
            f"Metric potential source-derived from full Janus: {decision['metric_potential_source_derived_from_full_janus']}",
            f"Full tensor Weyl closed: {decision['full_tensor_weyl_closed']}",
            f"Prediction ready: {decision['prediction_ready']}",
            "",
        ]
    )
    return "\n".join(lines)


def write_reports(report_path: Path = REPORT_PATH, json_path: Path = JSON_PATH) -> dict:
    payload = build_payload()
    report_path.parent.mkdir(parents=True, exist_ok=True)
    report_path.write_text(render_markdown(payload), encoding="utf-8")
    json_path.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    return payload


if __name__ == "__main__":
    write_reports()
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {JSON_PATH}")
