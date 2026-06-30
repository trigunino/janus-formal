from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_eft_volume_lambda_orientation_closure.md")
JSON_PATH = Path("outputs/reports/p0_eft_volume_lambda_orientation_closure.json")


def build_payload() -> dict:
    orientation = {
        "normal_choice": "n points from the minus sheet to the plus sheet across Sigma",
        "jump_definition": "Delta_log_det_E = log(det(E_plus)/det(E_minus))",
        "boundary_action_sign": "S_vol is added with the sign that cancels the outward trace flux",
        "flux_equation": "4*q_T*Delta_log_det_E + lambda*Delta_log_det_E = 0",
        "result": "lambda = -4*q_T for Delta_log_det_E != 0",
    }
    theorem_status = {
        "normal_orientation_fixed": True,
        "jump_orientation_fixed": True,
        "boundary_action_sign_fixed": True,
        "lambda_equals_minus_four_qT_derived": True,
        "volume_identity_channel_closed": True,
        "prediction_ready": False,
    }
    obligations = [
        "propagate lambda closure back into full RUN 1 with kappa and beta",
        "derive or orient-fix kappa and beta normalizations with the same convention",
        "then combine RUN 1 with RUN 2 before changing prediction_ready",
    ]
    return {
        "description": "Orientation closure for lambda=-4*q_T in the volume/solder boundary term.",
        "status": "lambda-orientation-closed-run1-combination-pending",
        "orientation": orientation,
        "theorem_status": theorem_status,
        "obligations": obligations,
        "verdict": (
            "With the Janus normal and boundary-action orientation fixed, the volume/solder "
            "term derives lambda=-4*q_T and closes the identity channel. Full prediction still "
            "waits on kappa/beta normalization and combined RUN 1/RUN 2 closure."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 EFT Volume Lambda Orientation Closure",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        "",
        "## Orientation",
    ]
    lines.extend(f"- {key}: {value}" for key, value in payload["orientation"].items())
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
