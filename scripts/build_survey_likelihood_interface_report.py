from __future__ import annotations

from collections.abc import Iterable
from pathlib import Path
import json

import numpy as np

from janus_lab.statistics import fixed_prediction_chi_square


REPORT_PATH = Path("outputs/reports/survey_likelihood_interface.md")
JSON_PATH = Path("outputs/reports/survey_likelihood_interface.json")

REQUIRED_SURVEY_INPUTS = (
    ("n_z", "source redshift distribution n(z)", "lensing kernel"),
    ("tomographic_bins", "tomographic bins", "survey binning"),
    ("observed_vector", "observed data vector", "likelihood residual"),
    ("covariance", "full positive-definite covariance", "likelihood normalization"),
    ("mask_window", "mask/window treatment", "mode coupling and survey footprint"),
)


def build_survey_input_checklist(
    available_inputs: Iterable[str] | None = None,
) -> list[dict[str, object]]:
    available = set(available_inputs or ())
    return [
        {
            "key": key,
            "input": label,
            "present": key in available,
            "blocks_prediction_label": key not in available,
            "required_for": required_for,
        }
        for key, label, required_for in REQUIRED_SURVEY_INPUTS
    ]


def require_survey_layer_ready(payload: dict) -> None:
    if payload.get("survey_layer_ready") is True:
        return
    missing = payload.get("missing_survey_inputs") or ["unknown_survey_input"]
    raise RuntimeError(
        "Survey layer is absent: missing "
        + ", ".join(str(item) for item in missing)
        + ". Refusing to label outputs as predictions."
    )


def build_payload(available_inputs: Iterable[str] | None = None) -> dict:
    checklist = build_survey_input_checklist(available_inputs)
    missing_inputs = [str(item["key"]) for item in checklist if not item["present"]]
    survey_layer_ready = not missing_inputs
    self_test = fixed_prediction_chi_square(
        "identity_self_test",
        np.asarray([1.0, 2.0]),
        np.asarray([1.0, 2.0]),
        np.eye(2),
    )
    return {
        "description": "Survey likelihood interface for fixed Janus predictions.",
        "requirements": [
            "declared source redshift distribution n(z)",
            "tomographic bins",
            "observed data vector",
            "prediction vector computed before comparison",
            "full positive-definite covariance",
            "mask/window treatment",
            "declared number of fitted nuisance parameters, usually zero for no-fit tests",
        ],
        "survey_input_checklist": checklist,
        "missing_survey_inputs": missing_inputs,
        "survey_layer_ready": survey_layer_ready,
        "can_call_outputs_predictions": survey_layer_ready,
        "implemented_function": "fixed_prediction_chi_square",
        "self_test_chi2": self_test.chi2,
        "self_test_n_params": self_test.n_params,
        "boundary": (
            "Interface only. The self-test uses identity data and is not evidence. "
            "No survey result is produced until n(z), bins, observed vector, covariance "
            "and mask/window are supplied."
        ),
    }


def main() -> None:
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    payload = build_payload()
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Survey Likelihood Interface",
        "",
        payload["description"],
        "",
        "| requirement |",
        "|---|",
    ]
    for item in payload["requirements"]:
        lines.append(f"| {item} |")
    lines.extend(["", "## Survey Input Checklist", ""])
    lines.append("| key | present | blocks prediction label |")
    lines.append("|---|---|---|")
    for item in payload["survey_input_checklist"]:
        lines.append(
            f"| {item['key']} | {item['present']} | "
            f"{item['blocks_prediction_label']} |"
        )
    lines.extend(
        [
            "",
            f"Implemented function: `{payload['implemented_function']}`.",
            f"Self-test chi2: `{payload['self_test_chi2']:.6g}`.",
            f"Survey layer ready: `{payload['survey_layer_ready']}`.",
            f"Can call outputs predictions: `{payload['can_call_outputs_predictions']}`.",
            "",
            payload["boundary"],
            "",
        ]
    )
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {JSON_PATH}")


if __name__ == "__main__":
    main()
