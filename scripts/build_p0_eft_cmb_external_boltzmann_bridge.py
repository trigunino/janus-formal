from __future__ import annotations

from pathlib import Path
import json

try:
    from scripts.build_p0_eft_cmb_full_hierarchy_pre_likelihood import build_payload as pre_likelihood_payload
except ModuleNotFoundError:
    from build_p0_eft_cmb_full_hierarchy_pre_likelihood import build_payload as pre_likelihood_payload


REPORT_PATH = Path("outputs/reports/p0_eft_cmb_external_boltzmann_bridge.md")
JSON_PATH = Path("outputs/reports/p0_eft_cmb_external_boltzmann_bridge.json")


def build_payload() -> dict:
    pre = pre_likelihood_payload()
    required_inputs = [
        "background H_JanusHolst(a)",
        "Delta_Neff_Holst",
        "visibility g(z)",
        "mu_JH(k,a)",
        "Sigma_JH(k,a)",
        "primordial P_R(k)",
    ]
    expected_outputs = [
        "TT C_ell",
        "TE C_ell",
        "EE C_ell",
        "phi-phi lensing C_ell",
        "matter transfer T_m(k,z)",
    ]
    return {
        "description": "Bridge contract for validating the Janus-Holst CMB hierarchy against an external Boltzmann solver.",
        "status": "external-boltzmann-bridge-contract-written",
        "proxy_spectra_available": pre["tt_te_ee_lensing_proxy_computed"],
        "required_inputs": required_inputs,
        "expected_outputs": expected_outputs,
        "recommended_backend": "CLASS or CAMB fork with custom background and modified gravity source functions",
        "adapter_written": False,
        "external_solver_run": False,
        "external_validation_passed": False,
        "direct_cmb_likelihood_ready": False,
        "next_required": "implement a CLASS/CAMB adapter using this contract and compare TT/TE/EE/lensing outputs.",
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 EFT CMB External Boltzmann Bridge",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Recommended backend: {payload['recommended_backend']}",
        f"Adapter written: {payload['adapter_written']}",
        f"External solver run: {payload['external_solver_run']}",
        f"External validation passed: {payload['external_validation_passed']}",
        f"Direct CMB likelihood ready: {payload['direct_cmb_likelihood_ready']}",
        "",
        "## Required Inputs",
        "",
    ]
    lines.extend(f"- `{item}`" for item in payload["required_inputs"])
    lines.extend(["", "## Expected Outputs", ""])
    lines.extend(f"- `{item}`" for item in payload["expected_outputs"])
    lines.extend(["", "## Next", "", payload["next_required"], ""])
    return "\n".join(lines)


def write_reports(report_path: Path = REPORT_PATH, json_path: Path = JSON_PATH) -> dict:
    report_path.parent.mkdir(parents=True, exist_ok=True)
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
