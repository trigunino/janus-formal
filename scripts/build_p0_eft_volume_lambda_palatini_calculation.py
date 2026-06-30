from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_eft_volume_lambda_palatini_calculation.md")
JSON_PATH = Path("outputs/reports/p0_eft_volume_lambda_palatini_calculation.json")


def build_payload() -> dict:
    calculation = {
        "identity": "delta log det(E) = Tr(E^-1 delta E) = E_a^mu delta E_mu^a",
        "heaviside_volume": "log det(E)=log det(E_-)+Theta(n)*Delta_log_det_E",
        "delta_source": "partial_n log det(E)=Delta_log_det_E*delta(n)",
        "trace_torsion_definition": "T_trace = q_T * partial_n log det(E)",
        "spinor_identity_channel": "Dirac trace shell contributes 4*q_T*Delta_log_det_E*I",
    }
    sign_audit = {
        "target_counterterm": "M_vol = lambda*Delta_log_det_E*I",
        "cancellation_equation": "4*q_T*Delta_log_det_E + lambda*Delta_log_det_E = 0",
        "derived_if_delta_nonzero": "lambda = -4*q_T",
        "sign_depends_on": "normal orientation and whether S_vol is added to or subtracted from the boundary action",
        "status": "magnitude fixed; sign fixed only after boundary-action orientation convention",
    }
    theorem_status = {
        "palatini_volume_variation_performed": True,
        "delta_source_extracted": True,
        "factor_four_derived_from_dirac_dimension": True,
        "lambda_magnitude_fixed": True,
        "lambda_sign_requires_orientation_convention": True,
        "lambda_equals_minus_four_qT_fully_derived": False,
        "prediction_ready": False,
    }
    obligations = [
        "fix the boundary action orientation convention for S_vol",
        "fix the normal orientation sign used by Delta_log_det_E",
        "then promote lambda=-4*q_T from cancellation identity to oriented geometric identity",
    ]
    return {
        "description": "Palatini/tetrad calculation for the volume-solder lambda coefficient.",
        "status": "lambda-magnitude-derived-sign-orientation-open",
        "calculation": calculation,
        "sign_audit": sign_audit,
        "theorem_status": theorem_status,
        "obligations": obligations,
        "verdict": (
            "The Palatini volume calculation derives the delta source and the factor 4. "
            "It fixes |lambda|=4|q_T| through the identity-channel cancellation. The remaining "
            "sign is an orientation convention for the boundary action and normal."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 EFT Volume Lambda Palatini Calculation",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        "",
        "## Calculation",
    ]
    lines.extend(f"- {key}: {value}" for key, value in payload["calculation"].items())
    lines.extend(["", "## Sign Audit"])
    lines.extend(f"- {key}: {value}" for key, value in payload["sign_audit"].items())
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
