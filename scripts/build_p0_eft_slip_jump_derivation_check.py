from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_eft_slip_jump_derivation_check.md")
JSON_PATH = Path("outputs/reports/p0_eft_slip_jump_derivation_check.json")


def build_payload() -> dict:
    jump_equations = {
        "hamilton_constraint": "relates Delta(partial_n Psi) to surface density/source trace",
        "spatial_stf_constraint": "relates Delta(partial_n(Psi-Phi)) to boundary anisotropic stress",
        "trace_spatial_constraint": "relates trace pressure to surface curvature/tension response",
        "important_distinction": "jump equations naturally fix normal derivatives, not Psi-Phi itself",
    }
    target = {
        "encoded_slip_target": "Psi|Sigma - Phi|Sigma = (3/2)*H*(beta*Delta_chi + lambda)",
        "run1_substitution": "(3/2)*H*(-sigma*(1+tau)/2 - 4*q_T)",
        "derived_directly": False,
        "reason": "requires converting derivative jump to value jump via boundary Green function or normal-mode profile",
    }
    theorem_status = {
        "perturbed_jump_structure_encoded": True,
        "stf_anisotropic_source_identified": True,
        "run1_source_substituted": True,
        "derivative_jump_slip_source_closed": True,
        "algebraic_value_slip_derived": False,
        "requires_boundary_green_function_or_normal_mode": True,
        "lensing_growth_sources_closed": False,
        "prediction_ready_unconditional": False,
    }
    obligations = [
        "derive the boundary Green function or normal-mode profile converting Delta(partial_n(Psi-Phi)) to Psi-Phi",
        "or downgrade the observable target to derivative-slip/junction-slip rather than value-slip",
        "then propagate to lensing potential Phi+Psi",
    ]
    return {
        "description": "Perturbed Einstein-Palatini jump derivation check for boundary slip.",
        "status": "derivative-slip-closed-value-slip-open",
        "jump_equations": jump_equations,
        "target": target,
        "theorem_status": theorem_status,
        "obligations": obligations,
        "verdict": (
            "The perturbed jump equations close the derivative-slip source, not the algebraic "
            "value-slip formula. A boundary Green function or normal-mode profile is needed "
            "before using Psi-Phi directly in lensing."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 EFT Slip Jump Derivation Check",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        "",
        "## Jump Equations",
    ]
    lines.extend(f"- {key}: {value}" for key, value in payload["jump_equations"].items())
    lines.extend(["", "## Target"])
    lines.extend(f"- {key}: {value}" for key, value in payload["target"].items())
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
