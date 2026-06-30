from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_eft_ds3_green_kernel_audit.md")
JSON_PATH = Path("outputs/reports/p0_eft_ds3_green_kernel_audit.json")


def build_payload() -> dict:
    spectral = {
        "operator": "O_Sigma = -Delta_dS3 + M_eff^2",
        "mass_gap": "M_eff^2 candidate = R/4 = (3/2)H^2",
        "green_kernel": "G(x,x') = sum_n psi_n(x) psi_n*(x')/(lambda_n+M_eff^2)",
        "coincident_limit": "G(x,x) needs regularization/renormalization",
        "target": "renormalized Neumann response G_Neumann^Sigma ?= (3/2)H",
    }
    modes = {
        "kink_only": "uses Delta(partial_n S)=Source_bnd directly; no coincident Green required",
        "value_connected": "requires a renormalized coincident or projected Green kernel",
        "risk": "coincident Green can include scheme-dependent or horizon-log terms",
    }
    theorem_status = {
        "spectral_operator_defined": True,
        "mass_gap_identified": True,
        "kink_only_observable_ready_conditionally": True,
        "coincident_green_requires_regularization": True,
        "green_kernel_equals_three_halves_H_proved": False,
        "value_slip_ready": False,
        "prediction_ready_unconditional": False,
    }
    obligations = [
        "choose the Green regularization scheme for coincident dS3 kernel",
        "compute the projected Neumann response, not the raw divergent G(x,x)",
        "check for horizon-log corrections before using (3/2)H",
        "use kink-only lensing as the safe observable branch meanwhile",
    ]
    return {
        "description": "dS3 Green kernel audit for converting derivative slip to value slip.",
        "status": "kink-ready-value-green-regularization-open",
        "spectral": spectral,
        "modes": modes,
        "theorem_status": theorem_status,
        "obligations": obligations,
        "verdict": (
            "The dS3 mass gap gives the right H scale, but the coincident Green kernel is a "
            "renormalized object. Kink-only lensing is the safe branch; value-slip with (3/2)H "
            "remains conditional on a Green-kernel scheme and calculation."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 EFT dS3 Green Kernel Audit",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        "",
        "## Spectral",
    ]
    lines.extend(f"- {key}: {value}" for key, value in payload["spectral"].items())
    lines.extend(["", "## Modes"])
    lines.extend(f"- {key}: {value}" for key, value in payload["modes"].items())
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
