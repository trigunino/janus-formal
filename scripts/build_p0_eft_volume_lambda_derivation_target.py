from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_eft_volume_lambda_derivation_target.md")
JSON_PATH = Path("outputs/reports/p0_eft_volume_lambda_derivation_target.json")


def build_payload() -> dict:
    derivation_target = {
        "bulk_measure": "det(E(x)) with Heaviside jump across Sigma",
        "log_jump": "Delta_log_det_E = log(det(E_plus)/det(E_minus))",
        "localized_source": "partial_n log(det E) = Delta_log_det_E * delta(Sigma)",
        "trace_torsion_link": "T_trace = q_T * partial log(det E)",
        "lambda_target": "lambda + 4*q_T = 0",
    }
    factor_four_audit = {
        "allowed_sources": [
            "Dirac spinor trace dimension tr(I_4)=4",
            "four-dimensional tetrad volume variation delta log det(E)=E_a^mu delta E_mu^a",
        ],
        "forbidden_source": "manual insertion of 4 just to cancel RUN 1",
        "current_status": "factor source identified but not derived by Palatini calculation",
    }
    theorem_status = {
        "volume_jump_mechanism_encoded": True,
        "lambda_target_encoded": True,
        "factor_four_audit_encoded": True,
        "palatini_variation_performed": False,
        "lambda_equals_minus_four_qT_derived": False,
        "pure_volume_closure_proved": False,
        "prediction_ready": False,
    }
    obligations = [
        "perform the Palatini/tetrad variation with discontinuous det(E)",
        "extract the delta(Sigma) coefficient in the spinor surface equation",
        "prove the factor 4 comes from Dirac trace or 4D tetrad volume variation",
        "prove lambda + 4*q_T = 0 as an identity, not as a solved parameter",
    ]
    return {
        "description": "Derivation target for lambda=-4*q_T from the Janus volume/solder measure.",
        "status": "lambda-derivation-target-open",
        "derivation_target": derivation_target,
        "factor_four_audit": factor_four_audit,
        "theorem_status": theorem_status,
        "obligations": obligations,
        "verdict": (
            "The volume/solder invariant is structurally able to close the identity channel. "
            "The remaining proof is a Palatini/tetrad variation that derives lambda=-4*q_T."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 EFT Volume Lambda Derivation Target",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        "",
        "## Derivation Target",
    ]
    lines.extend(f"- {key}: {value}" for key, value in payload["derivation_target"].items())
    lines.extend(["", "## Factor Four Audit"])
    lines.extend(f"- {key}: {value}" for key, value in payload["factor_four_audit"].items())
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
