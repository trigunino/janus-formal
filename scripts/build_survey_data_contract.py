from __future__ import annotations

from pathlib import Path
import json

import numpy as np


REPORT_PATH = Path("outputs/reports/survey_data_contract.md")
JSON_PATH = Path("outputs/reports/survey_data_contract.json")

REQUIRED_KEYS = (
    "survey_id",
    "observable_name",
    "n_z",
    "tomographic_bins",
    "observed_vector",
    "prediction_vector_id",
    "covariance",
    "mask_window",
    "nuisance_parameters_declared",
    "n_fit_parameters",
)


def _as_float_array(value, name: str) -> np.ndarray:
    try:
        array = np.asarray(value, dtype=float)
    except (TypeError, ValueError) as exc:
        raise ValueError(f"{name} must be numeric.") from exc
    if array.size == 0:
        raise ValueError(f"{name} must not be empty.")
    return array


def validate_survey_contract(contract: dict | None) -> dict:
    if contract is None:
        return {
            "ready": False,
            "missing": list(REQUIRED_KEYS),
            "errors": [],
            "dimension": None,
        }

    missing = [key for key in REQUIRED_KEYS if key not in contract]
    errors: list[str] = []
    dimension = None

    if "n_z" in contract:
        try:
            z = _as_float_array(contract["n_z"].get("z"), "n_z.z")
            weights = _as_float_array(contract["n_z"].get("weights"), "n_z.weights")
            if z.shape != weights.shape:
                errors.append("n_z.z and n_z.weights must have the same shape")
            if np.any(z < 0.0):
                errors.append("n_z.z must be non-negative")
            if np.any(weights < 0.0) or float(np.sum(weights)) <= 0.0:
                errors.append("n_z.weights must be non-negative with positive sum")
        except AttributeError:
            errors.append("n_z must be an object with z and weights")
        except ValueError as exc:
            errors.append(str(exc))

    if "tomographic_bins" in contract:
        bins = contract["tomographic_bins"]
        if not isinstance(bins, list) or not bins:
            errors.append("tomographic_bins must be a non-empty list")
        else:
            for index, item in enumerate(bins):
                try:
                    z_min = float(item["z_min"])
                    z_max = float(item["z_max"])
                    if z_min < 0.0 or z_max <= z_min:
                        errors.append(f"tomographic_bins[{index}] must satisfy 0 <= z_min < z_max")
                except (KeyError, TypeError, ValueError):
                    errors.append(f"tomographic_bins[{index}] must contain numeric z_min and z_max")

    for key in ("survey_id", "observable_name", "prediction_vector_id"):
        if key in contract and not str(contract[key]).strip():
            errors.append(f"{key} must be non-empty")

    if "observed_vector" in contract:
        try:
            observed = _as_float_array(contract["observed_vector"], "observed_vector")
            if observed.ndim != 1:
                errors.append("observed_vector must be one-dimensional")
            else:
                dimension = int(observed.shape[0])
        except ValueError as exc:
            errors.append(str(exc))

    if "covariance" in contract:
        try:
            covariance = _as_float_array(contract["covariance"], "covariance")
            if covariance.ndim != 2 or covariance.shape[0] != covariance.shape[1]:
                errors.append("covariance must be square")
            elif dimension is not None and covariance.shape[0] != dimension:
                errors.append("covariance dimension must match observed_vector")
            elif not np.allclose(covariance, covariance.T):
                errors.append("covariance must be symmetric")
            else:
                try:
                    np.linalg.cholesky(covariance)
                except np.linalg.LinAlgError:
                    errors.append("covariance must be positive definite")
        except ValueError as exc:
            errors.append(str(exc))

    if "mask_window" in contract:
        mask = contract["mask_window"]
        if not isinstance(mask, dict) or not (
            mask.get("description") or mask.get("path") or mask.get("window_matrix")
        ):
            errors.append("mask_window must declare description, path, or window_matrix")

    if "nuisance_parameters_declared" in contract and not isinstance(
        contract["nuisance_parameters_declared"],
        list,
    ):
        errors.append("nuisance_parameters_declared must be a list")

    if "n_fit_parameters" in contract:
        try:
            n_fit = int(contract["n_fit_parameters"])
            if n_fit != 0:
                errors.append("n_fit_parameters must be zero for no-fit tests")
        except (TypeError, ValueError):
            errors.append("n_fit_parameters must be an integer")

    return {
        "ready": not missing and not errors,
        "missing": missing,
        "errors": errors,
        "dimension": dimension,
    }


def build_payload(contract: dict | None = None) -> dict:
    validation = validate_survey_contract(contract)
    return {
        "description": "No-fit survey data contract for Janus prediction comparisons.",
        "required_keys": list(REQUIRED_KEYS),
        "validation": validation,
        "prediction_vector_rule": "Prediction vector must be computed before comparison and must not be fitted to the observed vector.",
        "nuisance_parameter_rule": "Declare nuisance parameters explicitly; n_fit_parameters must be zero for strict no-fit tests.",
        "survey_layer_ready": validation["ready"],
        "verdict": (
            "Survey contract is structurally ready."
            if validation["ready"]
            else "No survey prediction label is allowed until the contract is complete and valid."
        ),
    }


def render_markdown(payload: dict) -> str:
    validation = payload["validation"]
    lines = [
        "# Survey Data Contract",
        "",
        payload["description"],
        "",
        f"Survey layer ready: `{payload['survey_layer_ready']}`",
        "",
        "## Required Keys",
        "",
    ]
    lines.extend(f"- `{key}`" for key in payload["required_keys"])
    lines.extend(["", "## Validation", ""])
    lines.append(f"- missing: `{validation['missing']}`")
    lines.append(f"- errors: `{validation['errors']}`")
    lines.append(f"- dimension: `{validation['dimension']}`")
    lines.extend(
        [
            "",
            f"Prediction vector rule: {payload['prediction_vector_rule']}",
            f"Nuisance parameter rule: {payload['nuisance_parameter_rule']}",
            "",
            f"Verdict: {payload['verdict']}",
            "",
        ]
    )
    return "\n".join(lines)


def main() -> None:
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    payload = build_payload()
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(render_markdown(payload), encoding="utf-8")
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {JSON_PATH}")


if __name__ == "__main__":
    main()
